module Transform
  -- Fusable transformations
  ( betaReduce
  , etaReduce
  , inlineUnfolding
  , inlineLocal
  , caseReduce
  , extractLambda
  , caseDistribute
  , undefaultCase
  , redundantCase

  -- Stand-alone transformations
  , normalize
  , caseDedup
  , caseMerge
  , normalizeCaseOrder

  -- Helper function
  , reorderCase
  , compareScrut
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Map.Expr (CoreMap, eqCoreExpr, lookupTM, insertTM, emptyTM)
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
import GHC.Core.Opt.Simplify.Env (SimplMode (..))
import GHC.Core.Opt.Simplify.Utils (mkCase)
import GHC.MonadCore

import Data.List (nubBy, elemIndex, foldl')
import Data.Maybe (fromMaybe, fromJust)
import Data.Generics hiding (empty, GT)

import Control.Monad (guard, forM, (>=>))
import Control.Monad.Trans.Maybe (runMaybeT)
import Control.Applicative (Alternative (..), empty, asum)

import Types
import Simplify
import Util

-- TODO: Maybe we should make an alteration to the fixpoint run: allow it
-- to track state during the traversal. That way, we can make stuff like
-- the reordering, caseMerging or caseOrderCanolicalisation as a fix pass
-- as well instead of leaving it as its own traversal! Perhaps an environment
-- like the following will do? Of course, we can extend it however we like.
-- The important thing is to allow some 'tracking' function that always runs
-- during any layer in the traversal and attaches this info.
--
-- data Env = Env
--   { guts :: ModGuts
--   , inScope :: InScopeSet
--   , scruts :: CoreMap (AltCon, [CoreBndr])
--   }
--
-- Should the InScopeSet change when we inline an unfolding? Not sure if we
-- need to track global identifiers inside of expressions? If we do need to do
-- this, it might be very annoying as we cannot simply track the set with just
-- a backtracking esque algorithm. From what I've found, we don't need to track
-- global variables, which should make inlines safe as they should not introduce
-- free local variables.

-- | Normalizes an expression
normalize :: MonadCore m => MonadMod m => Pass m CoreExpr
normalize = do
  let fused = fuse
        [ betaReduce
        , inlineUnfolding
        , inlineLocal
        , caseDistribute
        , caseReduce
        , redundantCase
        , extractLambda
        , undefaultCase
        , etaReduce
        ]

  let withOccurAnal = (fmap occurAnalyseExpr .)
  let passes = withOccurAnal <$>
        [ fix fused
        , normalizeCaseOrder
        , fix betaReduce
        , caseDedup
        , caseMerge
        , fix redundantCase
        ]

  foldl' (>=>) pure passes

  -- e0 <- occurAnalyseExpr <$> fix fused expr
  -- e1 <- occurAnalyseExpr <$> normalizeCaseOrder e0
  -- e2 <- occurAnalyseExpr <$> fix redundantCase e1
  -- e3 <- occurAnalyseExpr <$> caseDedup e2
  -- occurAnalyseExpr <$> caseMerge e3

-- | Beta reduction
betaReduce :: Alternative m => Pass m CoreExpr
betaReduce = \case
  -- Normal beta reduction.
  App (Lam bind body) arg -> substitute body bind arg

  -- Reduction on let binding.
  Let (NonRec bind expr) body -> substitute body bind expr

  _ -> empty
  where
    -- | substitute e1 x e2 = e1[x:=e2]
    substitute :: Applicative m => CoreExpr -> CoreBndr -> CoreExpr -> m CoreExpr
    substitute body bind expr = do
      let inScope = mkInScopeSet $ exprFreeVars body `unionVarSet` exprFreeVars expr
      let subst = extendSubst (mkEmptySubst inScope) bind expr
      let body' = substExpr subst body
      pure body'

-- | Eta reduction
etaReduce :: Alternative m => Monad m => Pass m CoreExpr
etaReduce = \case
  Lam bind (App fun (Var arg)) -> do
    guard $ bind == arg
    let free = exprFreeVars fun
    guard . not $ bind `elemVarSet` free
    pure fun

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
caseReduce :: Alternative m => Monad m => Pass m CoreExpr
caseReduce = \case
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
    pure $ substExpr subst rhs

  _ -> empty
  where
    -- | Get the constructor spine (if available) of this expression with all
    -- the arguments that are applied to it.
    splitCon expr = do
      let (fun, args) = collectArgs expr

      -- Try to get the AltCon (if possible).
      con <- case fun of
        Var v | isDataConWorkId v -> pure $ DataAlt (idDataCon v)
        Lit l -> pure $ LitAlt l
        _ -> empty

      -- Trim the type arguments that do not appear on the match.
      let args' = trimConArgs con args
      pure (con, args')

-- | Extracts functions out of case statements. That is, for any case statement
-- that has a function type, we apply a fresh argument which we introduce with a
-- lambda.
extractLambda :: Alternative m => MonadCore m => Pass m CoreExpr
extractLambda  = \case
  Case scrut bind ty alts | Just (_, _, argTy, resTy) <- splitFunTy_maybe ty -> do
    var <- freshLocalVar "extracted" argTy
    let appAlt (Alt c bs rhs) = Alt c bs $ App rhs (Var var)
    let alts' = appAlt <$> alts
    let expr = Lam var $ Case scrut bind resTy alts'
    pure expr

  _ -> empty

-- | Distrubte expressions over a case.
--
-- This pushes case expressions towards the root of the expression.
caseDistribute :: Alternative m => MonadCore m => Pass m CoreExpr
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
    -- TODO: Does this really always give a unusued unique? What about if
    -- uniqAway was called inside of this expression? Make sure this doesn't
    -- mess up!
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
        pure $ substExpr subst expr

      _ -> empty

-- | Removes the default alternative in case statements. This only works for
-- data constructors, as these have a finite number of patterns, unlike for
-- example numeric literals.
undefaultCase :: Alternative m => MonadCore m => Pass m CoreExpr
undefaultCase = \case
  Case scrut bind ty alts -> do
    -- Get the dataconstructors for this scrutinee. Note that we only remove
    -- default cases for dataconstructors. That is, we cannot really do this
    -- in the same way for types with infinite constructors such as literals.
    let scrutTy = exprType scrut
    (tycon, _) <- maybeM $ tcSplitTyConApp_maybe scrutTy
    datacons <- maybeM $ tyConDataCons_maybe tycon

    -- Get the default value and remaining alts. We return empty if there
    -- doesn't exist a default branch.
    let (alts', def) = findDefault alts
    def' <- maybeM def

    -- Transforms the given dataconstructor into an 'excplicit' alternative.
    -- That is, the alt is never a default pattern.
    let toExplicit con = do
          let con' = DataAlt con
          let alt = findAlt con' alts'
          -- FIXME: The number of binders should match the arity of the
          -- constructor, even if we don't use the binders!
          let explicitDefault = Alt con' [] def'
          fromMaybe explicitDefault alt

    -- Make all alts explicit, such that no default branch exists in this case
    -- expression.
    let alts'' = toExplicit <$> datacons
    pure $ Case scrut bind ty alts''

  _ -> empty

-- | Removes obselete cases. That is, cases whose result will not change
-- depending on the value of the scrutinee.
redundantCase :: Alternative m => Monad m => Pass m CoreExpr
redundantCase = \case
  Case scrut bind _ alts -> do
    -- Check if all alts are equivalent, modulo free variables. Also returns
    -- this equivalent entry if it exists, as we'll use it later.
    -- FIXME: I don't think this comparison is always correct; we don't check
    -- whether the variables are bound by the alt in one expression but not in
    -- the other...
    let cmp (Alt _ _ rhs) (Alt _ _ rhs') = eqCoreExpr rhs rhs'
    expr <- case nubBy cmp alts of
      [Alt _ _ e] -> pure e
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
    pure $ substExpr subst expr

  _ -> empty

-- | Deduplicate case expressions.
--
-- Remove case expressions that scrutinize over the same expression. Note that
-- this does nothing for a nested case in the DEFAULT branch. We merge such
-- nested cases in a separate function.
--
-- FIXME: I think this breaks with variable shadowing. E.g we could deduplicate
-- terms that should not be deduplicated, or the substitution may bind the wrong
-- variables if they were defined somewhere inbetween.
-- The first case seems solvable, the second is a lot less easy. Maybe inspect
-- the GHC case simplifier to see how they do this. I know they also do case
-- deduplication, so maybe we can check that one out as well.
-- Alternatively, we can only deduplicate neighbouring cases. That way, we have
-- all the shadowing in scope. Only thing we would need to do then is make
-- sure case reordering puts duplicate cases next to each other.
caseDedup :: MonadCore m => Pass m CoreExpr
caseDedup = go emptyTM
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

              -- Extend the scrutinee map if we did not enter the default case.
              -- We track the same branch info for both the scrutinee itself
              -- and the binder.
              let extendList = foldl . flip $ uncurry insertTM
              let scruts' = case c of
                    DEFAULT -> scruts
                    _ -> extendList scruts
                      [ (scrut, (c, bs'))
                      , (Var bind, (c, bs'))
                      ]

              rhs' <- go scruts' rhs
              pure $ Alt c bs rhs'

        Case scrut bind ty <$> forM alts withAlt

      expr -> gmapM (mkM $ go scruts) expr

-- | Merges nested cases.
--
-- When a case has a DEFAULT pattern, any nested cases over the same scrutinee
-- cannot be deduplicated. As such, we instead merge the two cases. We reuse 
-- the GHC simplifier as it already has this mechanism implemented.
caseMerge :: MonadCore m => MonadMod m => Pass m CoreExpr
caseMerge = everywhereM $ mkM go
  where
    go = runSimplifier . \case
      Case scrut bind ty alts -> do
        let opts = (noOpSimplMode InitialPhase "CaseMerge")
              { sm_case_merge = True
              }
        mkCase opts scrut bind ty alts
      e -> pure e

-- | Reorders adjacent cases given a total ordering function.
reorderCase
  :: Alternative m
  => MonadCore m
  => ([Var] -> CoreExpr -> CoreExpr -> m ())
  -- ^ Comparison function of scrutinees.
  --
  -- Function that decides whether we should reorder the cases given these
  -- scrutinees. Should return empty if we do not want to swap. The first
  -- scrutinee is the current outer case, the second the current inner.
  --
  -- Note that if the ordering on this function is not total, repeated
  -- application of the case reordering will not normalise.
  -> Pass m CoreExpr
reorderCase shouldReorder = \case
  oCase@(Case oScrut oBind oTy oAlts) -> do
    -- Checks whether this alternative has an unbound case, and thus can be
    -- swapped.
    let unboundCase (Alt c bs rhs) = case rhs of
          expr@(Case scrut _ _ _) -> do
            -- Checks whether the cases are swappable
            guard $ exprFreeVars scrut `disjointVarSet` mkVarSet bs

            -- Checks whether we should reorder the cases, according to some
            -- ordering based on the scrutinees.
            shouldReorder bs oScrut scrut

            pure $ Alt c bs expr
          _ -> empty

    -- Get the unbound alt.
    Alt oCon oBinds iCase <- asum $ fmap unboundCase oAlts

    let clearOcc = flip setIdOccInfo noOccInfo

    -- We substitute the outer scrutinee binder in the inner case. We don't
    -- want reordering to block on case binders, thus we have to substitute to
    -- retain correctness.
    let inscope = mkInScopeSet $ exprFreeVars oCase
    -- TODO: What about the outer case binder here?
    let (subst, oBinds') = substBndrs (mkEmptySubst inscope) $ clearOcc <$> oBinds

    -- Inner case with substituted case binder. This pattern should never fail.
    -- It's mostly just easier to do substitution like this, than to have the
    -- case already split.
    (iScrut, iBind, iTy, iAlts) <- do
      let subst' = extendSubst subst oBind oScrut
      case substExpr subst' iCase of
        Case scrut bind ty alts -> pure (scrut, bind, ty, alts)
        _ -> empty

    -- Make the new inner case expression. We leave one branch as a temporary,
    -- which will be dictated by the new outer case.
    let ty = mkVisFunTysMany (varType <$> oBinds) oTy
    branch <- freshLocalVar "branch" ty
    let adjust (Alt c bs rhs)
          | oCon == c = let bs' = clearOcc <$> bs
                        in Alt c bs' $ foldl App (Var branch) (Var <$> bs')
          | otherwise = Alt c bs rhs
    let oAlts' = adjust <$> oAlts
    let inner = Lam branch $ Case oScrut oBind oTy oAlts'

    -- TODO: It seems we are somehow not binding all variables that we should.
    -- I think one thing that is wrong is the above substitution of the inner
    -- case: why aren't we substituting the wild variable in all leaves of the
    -- outer case? I think this is one thing that should be scrutinized.
    --
    -- Potentially, we can see *when* we miss a binding by checking the
    -- difference in free vars of the starting and pureed case expression.
    --
    -- Another thing; we don't really like the way we do the substitution
    -- currently. That is, ideally we do it immediately. This thing doesn't do
    -- beta reduction, so it hampers continuous reordering. Though I guess this
    -- is solved by the proposed change to the fixpoint passes.
    tmp <- freshLocalVar "tmp" $ exprType inner
    let (subst', iBind') = substBndr subst iBind
    let adjust' (Alt c bs rhs) = do
          let bs' = clearOcc <$> bs
          let (subst'', bs'') = substBndrs subst' bs'
          let rhs' = substExpr subst'' rhs
          -- TODO: Should this be a foldl or a foldr?
          let rhs'' = App (Var tmp) $ foldr Lam rhs' oBinds'
          -- dbg bs'
          -- dbg bs''
          -- dbg' "___________rhs:"
          -- dbg rhs
          -- dbg' "___________rhs':"
          -- dbg rhs'
          -- dbg' "___________rhs''':"
          -- dbg rhs''
          return $ Alt c bs'' rhs''
    -- let iAlts' = adjust' <$> iAlts
    -- dbg' "^^^^^^^^^^^dbg:"
    -- dbg subst'
    iAlts' <- mapM adjust' iAlts
    -- dbg iBind
    -- dbg $ head iAlts
    -- dbg $ head iAlts'

    let outer = Lam tmp $ Case iScrut iBind' iTy iAlts'
    let expr = App outer inner

    -- dbg' "===========start:"
    -- dbg oCase
    -- dbg' "-----------inner:"
    -- dbg inner
    -- dbg' "-----------outer:"
    -- dbg outer
    -- dbg' "-----------full:"
    -- dbg expr

    -- let fvBefore = exprFreeVars oCase
    -- let fvExpr = exprFreeVars expr
    -- case fvBefore == fvExpr of
    --   True -> pure ()
    --   False -> do
    --     dbg' "###################"
    --     dbg fvBefore
    --     dbg fvExpr
    --     error "Stopping! Incorrect expression..."

    -- -- -- The new expression, where the cases have swapped order.
    -- -- let expr = Case iScrut' iBind iTy iAlts''
    -- lintExpr' oCase >>= \case
    --   Just err -> do
    --     dbg' "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"
    --     dbg err
    --     error "Stopping! Starting case lint error..."
    --   Nothing -> pure ()

    -- lintExpr' inner >>= \case
    --   Just err -> do
    --     dbg' "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"
    --     dbg err
    --     error "Stopping! Inner lint error..."
    --   Nothing -> pure ()

    -- lintExpr' outer >>= \case
    --   Just err -> do
    --     dbg' "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"
    --     dbg err
    --     error "Stopping! Outer lint error..."
    --   Nothing -> pure ()

    -- lintExpr' expr >>= \case
    --   Just err -> do
    --     dbg' "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"
    --     dbg err
    --     error "Stopping! Lint error..."
    --   Nothing -> pure ()
    pure expr

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

  cmp lhs rhs

-- | Canonicalizes the ordering of cases.
--
-- FIXME: I don't think this really properly normalizes everything...
normalizeCaseOrder :: MonadCore m => Pass m CoreExpr
normalizeCaseOrder = go mempty
  where
    go :: MonadCore m => [Var] -> Pass m CoreExpr
    go vars = \case
      Case scrut bind ty alts -> do
        let goAlt (Alt c bs e) = do
              let vars' = bs <> vars
              e' <- go vars' e
              pure $ Alt c bs e'

        -- First normalize the order on the inner alts.
        expr <- Case scrut bind ty <$> mapM goAlt alts

        let cmp vs lhs rhs = do
              let vars' = vs <> vars
              let res = compareScrut vars' lhs rhs
              guard $ LT == res

        -- Then repeatedly reorder the current case.
        runMaybeT (reorderCase cmp expr) >>= \case
          Just expr' -> go vars expr'
          Nothing -> pure expr

      Lam bind expr -> Lam bind <$> go (bind:vars) expr

      expr -> gmapM (mkM $ go vars) expr
