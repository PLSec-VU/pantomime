module Transform
  -- Fusable transformations
  ( betaReduce
  , etaReduce
  , inlineUnfolding
  , inlineLocal
  , foldCase
  , extractLambda
  , caseDistribute
  , undefaultCase
  , redundantCase

  -- Stand-alone transformations
  , normalize
  , dedupCases
  , caseFactor
  , normalizeCaseOrder

  -- Helper function
  , reorderCase
  , bindPass
  , compareScrut
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Map.Expr (CoreMap, eqCoreExpr, lookupTM, insertTM, emptyTM)
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
import GHC.Tc.Utils.TcType (eqType)
import GHC.MonadCore

import Data.List (nubBy, elemIndex)
import Data.Maybe (fromMaybe, fromJust)
import Data.Generics hiding (empty, GT)

import Control.Monad.Trans.Maybe
import Control.Monad (guard, forM)
import Control.Applicative (Alternative (..), empty, asum)

import Types
import Util

-- | Maps an expression pass over a binder.
bindPass :: MonadCore m => Pass m (Expr a) -> Pass m (Bind' a)
bindPass f (Bind' x e) = Bind' x <$> f e

-- | Normalizes an expression
normalize :: MonadCore m => MonadMod m => Pass m CoreExpr
normalize e = do
  let fused = fuse
        [ betaReduce
        , inlineUnfolding
        , inlineLocal
        , caseDistribute
        , foldCase
        , redundantCase
        , extractLambda
        , undefaultCase
        , etaReduce
        ]

  e0 <- occurAnalyseExpr <$> fix fused e
  e1 <- occurAnalyseExpr <$> normalizeCaseOrder e0
  e2 <- occurAnalyseExpr <$> fix redundantCase e1
  occurAnalyseExpr <$> dedupCases e2

-- | Beta reduction
betaReduce :: (Alternative m, Monad m) => Pass m CoreExpr
betaReduce = \case
  -- Normal beta reduction.
  App (Lam bind body) arg -> substitute body bind arg

  -- Reduction on let binding.
  Let (NonRec bind expr) body -> substitute body bind expr

  _ -> empty
  where
    -- | substitute e1 x e2 = e1[x:=e2]
    substitute :: Monad m => CoreExpr -> CoreBndr -> CoreExpr -> m CoreExpr
    substitute body bind expr = do
      let inScope = mkInScopeSet $ exprFreeVars body `unionVarSet` exprFreeVars expr
      let subst = extendSubst (mkEmptySubst inScope) bind expr
      let body' = substExpr subst body
      return body'

-- | Eta reduction
etaReduce :: Alternative m => Monad m => Pass m CoreExpr
etaReduce = \case
  Lam bind (App fun (Var arg)) -> do
    guard $ bind == arg
    let free = exprFreeVars fun
    guard . not $ bind `elemVarSet` free
    return fun

  _ -> empty

-- | Inlines all non-typeclass functions.
inlineUnfolding :: Alternative m => Pass m CoreExpr
inlineUnfolding = \case
  Var x -> case idUnfolding x of
    CoreUnfolding { uf_tmpl } -> pure uf_tmpl
    DFunUnfolding { df_bndrs, df_con, df_args } -> do
      let con = Var $ dataConWorkId df_con
      let inner = foldl App con df_args
      let quantified = foldr Lam inner df_bndrs
      pure quantified
    _ -> empty
  _ -> empty

-- | Inline definitions that are local to the current module.
inlineLocal :: Alternative m => MonadMod m => Pass m CoreExpr
inlineLocal = \case
  Var x -> do
    Bind' _ e <- lookupLocal (== x)
    pure e
  _ -> empty

-- | Reduces a case expression if the spine of the scrutinee is a constructor.
foldCase :: (Alternative m, Monad m) => Pass m CoreExpr
foldCase = \case
  Case scrut bind _ alts -> do
    -- Get the spine if it is a constructor.
    (ac, es) <- splitCon scrut

    -- Get the alt matching this spine.
    Alt _ bs rhs <- maybeM $ findAlt ac alts

    -- Get the variables that are in scope already.
    let inscope = mkInScopeSet $ unionVarSets
          [ exprFreeVars rhs
          , exprFreeVars scrut
          , mkVarSet bs
          ]

    -- Map all the binders of the case to the expressions along the spine.
    -- Additionally, the binder should be substituted by the scrutinee.
    let errmsg = "arguments on constructor should be equivalent to binders in pattern"
    let mapping = (bind, scrut) : zipEqual errmsg bs es

    -- Make the substition using the mapping.
    let subst = extendSubstList (mkEmptySubst inscope) mapping

    -- Perform the substitution.
    return $ substExpr subst rhs

  _ -> empty
  where
    -- | Get the constructor spine (if available) of this expression with all
    -- the arguments that are applied to it.
    splitCon expr = do
      let (fun, args) = collectArgs expr

      -- Try to get the AltCon (if possible).
      con <- case fun of
        Var v | isDataConWorkId v -> return $ DataAlt (idDataCon v)
        Lit l -> return $ LitAlt l
        _ -> empty

      -- Trim the type arguments that do not appear on the match.
      let args' = trimConArgs con args
      return (con, args')

-- | Extracts functions out of case statements. That is, for any case statement
-- that has a function type, we apply a fresh argument which we introduce with a
-- lambda.
extractLambda :: (Alternative m, MonadCore m) => Pass m CoreExpr
extractLambda  = \case
  Case scrut bind ty alts | Just (_, _, argTy, resTy) <- splitFunTy_maybe ty -> do
    var <- freshLocalVar "extracted" argTy
    let appAlt (Alt c bs rhs) = Alt c bs $ App rhs (Var var)
    let alts' = appAlt <$> alts
    let expr = Lam var $ Case scrut bind resTy alts'
    return expr

  _ -> empty

-- | Distrubte expressions over a case.
--
-- This pushes case expressions towards the root of the expression.
caseDistribute :: (Alternative m, MonadCore m) => Pass m CoreExpr
caseDistribute = \case
  -- Nested case
  Case scrut@Case {} bind ty alts -> do
    temp <- tempVar $ exprType scrut
    let fun = Lam temp (Case (Var temp) bind ty alts)
    distribute fun scrut

  -- Inline argument into case
  App fun@Case {} arg -> do
    temp <- tempVar $ exprType fun
    let fun' = Lam temp (App (Var temp) arg)
    distribute fun' fun

  -- Inline function into case
  App fun arg@Case {} -> distribute fun arg

  _ -> empty
  where
    tempVar = freshLocalVar "temp"

    distribute fun = \case
      Case scrut bind _ alts -> do
        -- Create a temporary unique variable. We will substitute this variable
        -- for the given function using substExpr, which will make sure that all
        -- the variable renaming is correctly handled.
        temp <- tempVar $ exprType fun

        -- Distribute the temporary variable as the function to every rhs.
        let distribute' (Alt c bs rhs) = Alt c bs (App (Var temp) rhs)
        let alts' = distribute' <$> alts

        -- Get the type for the new case statement and create the new case.
        let ty = coreAltsType alts'
        let expr = Case scrut bind ty alts'

        -- Get all variables that are in scope
        let inscope = mkInScopeSet $ exprFreeVars expr `unionVarSet` exprFreeVars fun

        -- Use the in-scope set to make a substitution from the temporary
        -- argument to the given function.
        let subst = extendSubst (mkEmptySubst inscope) temp fun

        -- Substitute the temporary variable for the given function.
        return $ substExpr subst expr

      _ -> empty

-- | Removes the default alternative in case statements. This only works for
-- data constructors, as these have a finite number of patterns, unlike for
-- example numeric literals.
undefaultCase :: (Alternative m, MonadCore m) => Pass m CoreExpr
undefaultCase = \case
  Case scrut bind ty alts -> do
    -- Get the dataconstructors for this scrutinee. Note that we only remove
    -- default cases for dataconstructors. That is, we cannot really do this
    -- in the same way for types with infinite constructors such as literals.
    let scrutTy = exprType scrut
    (tycon, _) <- maybeM $ tcSplitTyConApp_maybe scrutTy
    datacons <- maybeM $ tyConDataCons_maybe tycon

    -- Get the default value and remaining alts. We return if there doesn't
    -- exist a default branch.
    let (alts', def) = findDefault alts
    def' <- maybeM def

    -- Transforms the given dataconstructor into an 'excplicit' alternative.
    -- That is, the alt is never a default pattern.
    let toExplicit con = do
          let con' = DataAlt con
          let alt = findAlt con' alts'
          let explicitDefault = Alt con' [] def'
          fromMaybe explicitDefault alt

    -- Make all alts explicit, such that no default branch exists in this case
    -- expression.
    let alts'' = toExplicit <$> datacons
    return $ Case scrut bind ty alts''

  _ -> empty

-- | Removes obselete cases. That is, cases whose result will not change
-- depending on the value of the scrutinee.o
redundantCase :: (Alternative m, Monad m) => Pass m CoreExpr
redundantCase = \case
  Case scrut bind _ alts -> do
    -- Check if all alts are equivalent, modulo free variables. Also returns
    -- this equivalent entry if it exists, as we'll use it later.
    let cmp (Alt _ _ rhs) (Alt _ _ rhs') = eqCoreExpr rhs rhs'
    expr <- case nubBy cmp alts of
      [Alt _ _ e] -> return e
      _ -> empty

    -- Check if all alts do not bind any of their pattern (which would make
    -- them not equivalent due to different binding variables).
    let unbound (Alt _ bs rhs) = exprFreeVars rhs `disjointVarSet` mkVarSet bs
    guard $ all unbound alts

    -- Get all free variables in this expression for the in-scope set.
    let inscope = mkInScopeSet $ exprFreeVars expr

    -- Use the in-scope set to make a substitution for the scrutinee.
    let subst = extendSubst (mkEmptySubst inscope) bind scrut

    -- Perform the substitution.
    return $ substExpr subst expr

  _ -> empty

-- | Deduplicate case expressions.
--
-- Remove case expressions that scrutinize over the same expression.
-- FIXME: I think there is an issue with the fold given a default branch:
-- we cannot always fold a branch in this case I think. Maybe we could do
-- something like include it in the outer case?
dedupCases :: MonadCore m => Pass m CoreExpr
dedupCases = go emptyTM
  where
    go :: MonadCore m => CoreMap (AltCon, [CoreBndr]) -> Pass m CoreExpr
    go scruts = \case
      -- We have previously case split over this scrutinee if we enter this
      -- case. Thus, we can remove the case split by selecting the branch
      -- that was taken previously. We take care of the binders in the term to
      -- reference the outer case.
      Case scrut bind _ alts | Just (c, bs) <- lookupTM scrut scruts -> do
        -- A matching alt should always be available.
        let Alt _ bs' rhs = fromJust $ findAlt c alts

        -- Map all the binders of the case to the expressions along the spine.
        -- Additionally, the binder should be substituted by the scrutinee.
        let mapping = (bind, scrut) : zip bs' (Var <$> bs)

        -- Get the inscope variables.
        let inscope = mkInScopeSet $ exprFreeVars rhs

        -- Make the substition using the mapping and perform the substitution.
        let subst = extendSubstList (mkEmptySubst inscope) mapping

        -- Substitute the alts in the expression.
        let expr = substExpr subst rhs

        -- Attempt to fold more cases in the new expression.
        go scruts expr

      -- We have not case split over this scrutinee before, thus we add it to
      -- the map and continue. We do not have to traverse the scrutinee itself
      -- for the fold in this scenario, as the case distribute pass makes sure
      -- that no scrutinee can contain a case.
      Case scrut bind ty alts -> do
        let withAlt (Alt c bs rhs) = do
              -- We remove the occurence info (may occur many times), as it may do
              -- so after deduplicating a case. The occurence analysis doesn't catch
              -- this, so we do it manually.
              let bs' = flip setIdOccInfo noOccInfo <$> bs
              -- We track the same branch info for both the scrutinee itself
              -- and the binder.
              let extendList = foldl . flip $ uncurry insertTM
              let scruts' = extendList scruts
                    [ (scrut, (c, bs'))
                    , (Var bind, (c, bs'))
                    ]
              rhs' <- go scruts' rhs
              return $ Alt c bs rhs'

        Case scrut bind ty <$> forM alts withAlt

      expr -> gmapM (mkM $ go scruts) expr

-- | Reorders adjacent cases given a total ordering function.
reorderCase
  :: (Alternative m, MonadCore m)
  => (CoreExpr -> CoreExpr -> m ())
  -- ^ Comparison function of scrutinees.
  --
  -- Function that decides whether we should reorder the cases given these
  -- scrutinees. Should return empty if we do not want to swap. The first
  -- scrutinee is the current outer case, the second the current inner.
  --
  -- Note that if the ordering on this function is not total, repeated
  -- applicatitation of the case reordering will not normalise.
  -> Pass m CoreExpr
reorderCase shouldReorder = \case
  Case oScrut oBind oTy oAlts -> do
    -- Checks whether this alternative has an unbound case, and thus can be
    -- swapped.
    let unboundCase (Alt c bs rhs) = case rhs of
          Case scrut bind ty alts -> do
            -- Checks whether the cases are swappable
            guard $ exprFreeVars scrut `disjointVarSet` mkVarSet bs

            -- Checks whether we should reorder the cases, according to some
            -- ordering based on the scrutinees.
            shouldReorder oScrut scrut

            return (c, bs, (scrut, bind, ty, alts))
          _ -> empty

    -- Get the unbound alt as an irrefutable pattern. Essentially this is just
    -- an Alt and Case, but not as sum type.
    (oCon, _, (iScrut, iBind, iTy, iAlts)) <- asum $ fmap unboundCase oAlts

    -- We substitute the outer scrutinee binder in the inner scrutinee, as
    -- otherwise this binder will appear unbound in the final expression.
    -- This may duplicate the outer scrutinee, but retains correctness of the
    -- reordering.
    let inscope = mkInScopeSet $ exprFreeVars iScrut
    let subst = extendSubst (mkEmptySubst inscope) oBind oScrut
    let iScrut' = substExpr subst iScrut

    -- Changes the given rhs of an inner alt to one where the order is swapped.
    -- That is, this will map the alt rhs to be the new outer case.
    let innerRhsToOuter irhs = do
          -- Helper function to change the old outer case to be the inner case.
          -- Specifically, if we match the original branch for the substitution,
          -- we should use the rhs of the old inner case.
          let adjust (Alt c bs rhs)
                | oCon == c = Alt c bs irhs
                | otherwise = Alt c bs rhs
          let oAlts' = adjust <$> oAlts
          Case oScrut oBind oTy oAlts'

    -- Map the rhs of an alt.
    let mapAlt f (Alt c bs rhs) = Alt c bs $ f rhs

    -- Map all inner alts to contain a modified copy of the outer alts. That is
    -- this will swap the ordering of the cases.
    let iAlts' = mapAlt innerRhsToOuter <$> iAlts

    -- The new expression, where the cases have swapped order.
    return $ Case iScrut' iBind iTy iAlts'

  _ -> empty

-- | Compares two scrutinees given some ordered in scope set. Note that the
-- scrutinees are expected to be normalised. Normalised scrutinees should only
-- contain variables, literals and their application.
--
-- The given ordered list of Id's decides ordering when comparing variables.
-- Global variables are ordered by their Unique.
--
-- The fine-grained ordering is only checked if both expressions only contain
-- local Id's in the given list. Otherwise, the list that doesn't fulfill this
-- condition is the smaller one. If this is the case for both, they're
-- considered equal.
compareScrut :: [Id] -> CoreExpr -> CoreExpr -> Ordering
compareScrut def lhs rhs = do
  let def' = mkVarSet def

  -- Returns true if there is a variable in the expression that is out of scope
  -- of the given Id list.
  let outOfScopeLocal expr = do
        let free = exprFreeIds expr
        not $ subVarSet free def'

  -- Finds the index of an id, if it exists
  let idIndex = flip elemIndex def

  -- Compares variables. We can compare local variables using the ordering
  -- defined by the Id list. The global names should be ordered across functions
  -- and as such retain total ordering on comparison.
  let cmpVar x y = case (idIndex x, idIndex y) of
        (Nothing, Nothing) -> compare x y
        (idx, idx') -> compare idx idx'

  -- Compares scrutinees. Note that at this point, we expect scrutinees to be
  -- normalized. Thus, we only provide comparison for the constructs we expect
  -- to be there. We use the given ordered Id list to order variable occurences.
  let cmp l r = case (l, r) of
        (Var x, Var y) -> cmpVar x y
        (Var _, _) -> GT
        (_, Var _) -> LT
        (Lit x, Lit y) -> compare x y
        (Lit _, _) -> GT
        (_, Lit _) -> LT
        (App f a, App f' a') -> cmp f a <> cmp f' a'
        _ -> EQ
  -- FIXME: I think this ordering doesn't really work for normalisation. It
  -- might be better to consider what is the 'lowest' variable in an expression,
  -- if this is equal, 'second lowest' etc. If all of this is equalt, then we
  -- should consider their order of appearance in the expression.
  --
  -- To be explicit; the total ordering should respect that some cases cannot
  -- be reordered (i.e. because the outer binds variables used in the inner
  -- scrutinee). The current comparison doesn't respect this property! Hopefully
  -- this proposed solution does.

  -- If both scrutinees don't have variables that are not in the id list, they
  -- should occur on the current 'layer' of cases. In this case, we reorder them
  -- according to content.
  case (outOfScopeLocal lhs, outOfScopeLocal rhs) of
    (False, False) -> cmp lhs rhs
    (l, r) -> compare l r

-- | Canonicalizes the ordering of cases.
normalizeCaseOrder :: MonadCore m => Pass m CoreExpr
normalizeCaseOrder = go mempty
  where
    go :: MonadCore m => [Var] -> Pass m CoreExpr
    go vars = \case
      expr@(Case scrut bind ty alts) -> do
        let cmp lhs rhs = guard $ GT == compareScrut vars lhs rhs
        let reorder = runMaybeT . reorderCase cmp

        let goAlt (Alt c bs e) = do
              let vars' = bs <> (bind:vars)
              e' <- go vars' e
              return $ Alt c bs e'

        maybeExpr <- reorder expr
        case maybeExpr of
          Just expr' -> go vars expr'
          Nothing -> Case scrut bind ty <$> mapM goAlt alts
      Lam bind expr -> Lam bind <$> go (bind:vars) expr
      expr -> gmapM (mkM $ go vars) expr

-- -- | Factor out applications in a case statement. This is roughly the inverse
-- -- operation of distributing a case.
-- caseFactor :: (Alternative m, MonadCore m) => Pass m CoreExpr
-- caseFactor = \case
--   cas@(Case scrut bind ty alts) -> do
--     let impossible = mkImpossibleExpr ty "impossible"

--     -- Get the first application in the alts. If there exists none, then we
--     -- simply return empty as we cannot distribute this case expression.
--     let getApp (Alt _ _ e@(App fun arg)) | not $ e `eqCoreExpr` impossible = return (fun, arg)
--         getApp _ = empty
--     (fun, arg) <- asum $ getApp <$> alts

--     dbg' "================"
--     dbg cas
--     dbg' "----------------"
--     dbg fun
--     dbg arg

--     -- TODO: We should get a better variable for an alternative.
--     let factor (App f a) = return (f, a)
--         factor e = case arg of
--           Type argTy -> do
--             let argKind = typeKind argTy
--             x <- freshTyVar "x" argKind
--             let e' = Lam x e
--             dbg $ exprType e'
--             return (e', arg)
--           _ -> do
--             let argTy = exprType arg
--             x <- freshLocalVar "x" argTy
--             let e' = Lam x e
--             let impossible' = mkImpossibleExpr (exprType arg) "impossible"
--             return (e', impossible')

--     let factor' (Alt c bs rhs) = do
--           (f, a) <- factor rhs
--           return (Alt c bs f, Alt c bs a)

--     let tyOrKind = \case
--           Type t -> typeKind t
--           e -> exprType e

--     (fAlts, aAlts) <- unzip <$> forM alts factor'

--     let cmp (Alt _ _ rhs) (Alt _ _ rhs') = tyOrKind rhs `eqType` tyOrKind rhs'
--     let equal as = length (nubBy cmp as) == 1

--     dbg $ equal fAlts
--     dbg $ equal aAlts


--     let fCase = Case scrut bind (tyOrKind fun) fAlts
--     let aCase = Case scrut bind (tyOrKind arg) aAlts

--     let expr = App fCase aCase 

--     dbg' "----------------"
--     dbg expr
--     return expr
--   _ -> empty

-- FIXME: This doesn't work. It should factor out applications to do inference,
-- but let's first implement tactics based approach.
caseFactor :: (Alternative m, MonadCore m) => Pass m CoreExpr
caseFactor = \case
  cas@(Case scrut bind ty alts) -> do
    let impossible = mkImpossibleExpr ty "impossible"

    -- Get the first application in the alts. If there exists none, then we
    -- simply return empty as we cannot distribute this case expression.
    let getApp (Alt _ _ rhs@(App fun arg))
          | not $ isTypeArg arg
          , not $ rhs `eqCoreExpr` impossible = return (fun, arg)
        getApp _ = empty
    (fun, arg) <- asum $ getApp <$> alts

    dbg' "================"
    dbg cas
    dbg' "----------------"
    dbg fun
    dbg arg

    -- TODO: We should get a better variable for an alternative.
    let factor (App f a) | not $ isTypeArg a = return (f, a)
        factor e = do
          let argTy = exprType arg
          x <- freshLocalVar "x" argTy
          let e' = Lam x e
          let impossible' = mkImpossibleExpr (exprType arg) "impossible"
          return (e', impossible')

    let factor' (Alt c bs rhs) = do
          (f, a) <- factor rhs
          return (Alt c bs f, Alt c bs a)

    let tyOrKind = \case
          Type t -> typeKind t
          e -> exprType e

    (fAlts, aAlts) <- unzip <$> forM alts factor'

    let cmp (Alt _ _ rhs) (Alt _ _ rhs') = tyOrKind rhs `eqType` tyOrKind rhs'
    let equal as = length (nubBy cmp as) == 1

    dbg $ equal fAlts
    dbg $ equal aAlts


    let fCase = Case scrut bind (tyOrKind fun) fAlts
    let aCase = Case scrut bind (tyOrKind arg) aAlts

    let expr = App fCase aCase

    dbg' "----------------"
    dbg expr
    empty
  _ -> empty

