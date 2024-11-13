module Transform
  -- Fusable transformations
  ( betaReduce
  , etaReduce
  , inlineUnfolding
  , inlineLocal
  , caseReduce
  , floatLambda
  , caseDistribute
  , undefaultCase
  , redundantCase
  , caseDedup
  , caseMerge
  , caseSwap
  , dropTick
  , dropReflCast
  , joinCasts
  , floatCast

  -- Stand-alone transformations
  , normalize

  -- Helper functions
  , compareScrut
  ) where

import GHC.Plugins hiding (empty, (<>), split)
import GHC.Core.Map.Expr (eqCoreExpr)
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
import GHC.Core.TyCo.Rep (Coercion (..))
import GHC.Core.Coercion.Opt
-- import GHC.Data.Pair
import GHC.MonadCore

import Data.List (nubBy, elemIndex)
import Data.Maybe (fromMaybe, isJust)

import Control.Monad (guard, forM)
import Control.Monad.Trans.Maybe (runMaybeT)
import Control.Monad.Reader (MonadReader, reader)
import Control.Applicative (Alternative (..), empty, asum)

import Types
import Fusion
import Util

-- | Normalizes an expression.
normalize
  :: MonadCore m
  => MonadReader r  m
  => HasModGuts r
  => Pass m CoreExpr
normalize expr = do
  let fused = fuse
        [ caseReduce
        , betaReduce
        , inlineUnfolding
        , inlineLocal
        , dropReflCast
        , joinCasts
        , floatCast
        -- , splitCast
        , dropTick
        , caseDistribute
        , redundantCase
        , floatLambda
        , undefaultCase
        , caseDedup
        , caseMerge
        , caseSwap
        ]

  let fixable e = do
        dbg' "============================="
        dbg e
        singlePass fused e

  occurAnalyseExpr <$> fix fixable expr
  -- occurAnalyseExpr <$> fixWithEnv fused expr

-- | Beta reduction
betaReduce
  :: MonadReader r m
  => HasInScopeSet r
  => Alternative m
  => Pass m CoreExpr
betaReduce = \case
  -- Normal beta reduction.
  App (Lam bind body) arg -> substitute body bind arg

  -- Reduction on let binding.
  Let (NonRec bind expr) body -> substitute body bind expr

  _ -> empty
  where
    -- | substitute e1 x e2 = e1[x:=e2]
    substitute body bind expr = do
      inScope <- reader inScopeSet
      let subst = extendSubst (mkEmptySubst inScope) bind expr
      let body' = substExpr subst body
      pure body'

-- | Eta reduction
--
-- FIXME: Somehow this breaks with linear type on Just? The linter can give an
-- error if we for example don't do beta reduction in the pass.
-- I think the error is that somehow \x -> f x types different from f, where
-- f has Mult that is not MultTy. Idk, I should look into this more, but eta
-- reduction is not really the most interesting transformation anyway..
etaReduce :: Alternative m => MonadCore m => Pass m CoreExpr
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
inlineLocal
  :: Alternative m
  => MonadReader r m
  => HasModGuts r
  => Pass m CoreExpr
inlineLocal = \case
  Var x -> do
    Bind' _ e <- lookupLocal (== x)
    pure e
  _ -> empty

-- | Reduces a case expression if the spine of the scrutinee is a constructor.
caseReduce :: Alternative m => MonadReader r m => HasInScopeSet r => Pass m CoreExpr
caseReduce = \case
  Case scrut bndr _ alts -> do
    -- | Get the constructor spine (if available) of this expression with all
    -- the arguments that are applied to it.
    let splitCon expr = do
          let (fun, args) = collectArgs expr

          -- Try to get the AltCon (if possible).
          con <- case fun of
            Var v | isDataConWorkId v -> pure $ DataAlt (idDataCon v)
            Lit l -> pure $ LitAlt l
            _ -> empty

          -- Trim the type arguments that do not appear on the match.
          let args' = trimConArgs con args
          pure (con, args')

    -- Get the spine if it is a constructor.
    (altcon, args) <- splitCon scrut

    -- Get the alt matching this spine.
    Alt _ bndrs rhs <- maybeM $ findAlt altcon alts

    -- Get the variables that are in scope already.
    inScope <- reader inScopeSet
    let bndrs' = bndr : bndrs
    let inScope' = extendInScopeSetList inScope bndrs'

    -- Map all the binders of the case to the expressions along the spine.
    -- Additionally, we substute the binder for the scrutinee.
    let mapping = zip bndrs' $ scrut : args

    -- Make the substition using the mapping.
    let subst = extendSubstList (mkEmptySubst inScope') mapping

    -- Perform the substitution.
    pure $ substExpr subst rhs

  _ -> empty

-- | Extracts functions out of case statements. That is, for any case statement
-- that has a function type, we apply a fresh argument which we introduce with a
-- lambda.
--
-- TODO: I don't think I need the call to freshLocalVar here.
floatLambda :: Alternative m => MonadCore m => Pass m CoreExpr
floatLambda  = \case
  Case scrut bind ty alts | Just (_, mult, argTy, resTy) <- splitFunTy_maybe ty -> do
    var <- freshLocalVar "floated" mult argTy
    let appAlt (Alt c bs rhs) = Alt c bs $ App rhs (Var var)
    let alts' = appAlt <$> alts
    let expr = Lam var $ Case scrut bind resTy alts'
    pure expr

  _ -> empty

-- | Remove ticks from the expression.
dropTick :: Alternative m => Pass m CoreExpr
dropTick = \case
  Tick _ e -> pure e
  _ -> empty

-- | Remove reflexive casts.
--
-- Reflexive casts are essentially no-ops.
dropReflCast :: Alternative m => Pass m CoreExpr
dropReflCast = \case
  Cast expr co | isReflexiveCo co -> pure expr

  _ -> empty

-- | Join two consecutive casts.
--
-- Merging casts is good both for normalisation and potentially eliminating
-- casts that become reflective by this operation.
joinCasts :: Alternative m => MonadReader r m => HasInScopeSet r => Pass m CoreExpr
joinCasts = \case
  Cast (Cast expr co) co' -> do
    inScope <- reader inScopeSet
    let subst = mkEmptySubst inScope
    let co'' = optCoercion (OptCoercionOpts True) subst (TransCo co co')
    pure $ Cast expr co''

  _ -> empty

-- | Float casts over applications.
--
-- This allows more reductions to be able to take place.
floatCast :: Alternative m => MonadReader r m => HasInScopeSet r => Pass m CoreExpr
floatCast = \case
  App (Cast fun FunCo { fco_arg, fco_res }) arg -> do
    let arg' = Cast arg fco_arg
    pure $ Cast (App fun arg') fco_res

  App (Cast fun (ForAllCo bndr argCo resCo)) (Type arg) -> do
    inScope <- reader inScopeSet
    let subst0 = mkEmptySubst inScope
    let subst1 = extendTvSubst subst0 bndr arg

    let argCo' = substCo subst1 argCo
    let resCo' = substCo subst1 resCo

    let arg' = Type $ mkCastTy arg argCo'

    pure $ Cast (App fun arg') resCo'

  _ -> empty

-- | Distrubte expressions over a case.
--
-- This pushes case expressions towards the root of the expression.
caseDistribute :: Alternative m => MonadReader r m => HasInScopeSet r => Pass m CoreExpr
caseDistribute = \case
  -- Nested case
  Case scrut@Case {} bind ty alts ->
    distribute (\rhs -> Case rhs bind ty alts) scrut
--     let fun = Lam temp (Case (Var temp) bind ty alts)

  -- Inline argument into case
  App fun@Case {} arg -> distribute (flip App arg) fun

  -- Inline function into case
  App fun arg@Case {} -> distribute (App fun) arg

  -- Inline cast into case
  Cast expr@Case {} coercion -> distribute (flip Cast coercion) expr

  _ -> empty
  where
    distribute f = \case
      Case scrut bndr _ alts -> do
        -- Create initial substitution map and substitute the case binder.
        inScope <- reader inScopeSet
        let subst0 = mkEmptySubst inScope
        let (subst1, bndr') = substBndr subst0 bndr

        -- For every alternative, we substitute its binders and right-hand-side.
        -- Since all binders are now non-clashing with previously defined ones,
        -- we can call our helper function that actually distributes without
        -- worrying about variable capturing.
        let alts' = flip fmap alts $ \(Alt con bndrs rhs) -> do
              let (subst2, bndrs') = substBndrs subst1 bndrs
              let rhs' = substExpr subst2 rhs
              Alt con bndrs' (f rhs')

        -- Get the type of the new alternatives
        let ty' = coreAltsType alts'

        -- Return the new case expression, with adjusted alts.
        pure $ Case scrut bndr' ty' alts'

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
    let (explicit, def) = findDefault alts
    def' <- maybeM def

    -- Transforms the given dataconstructor into an 'explicit' alternative.
    -- That is, the alt is never a default pattern.
    let toExplicit con = do
          let con' = DataAlt con
          let alt = findAlt con' explicit
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
redundantCase
  :: Alternative m
  => MonadReader r m
  => HasInScopeSet r
  => Pass m CoreExpr
redundantCase = \case
  Case scrut bind _ alts -> do
    -- Check if all alts do not bind any of their pattern (which would make
    -- them not equivalent due to different binding variables).
    let unbound (Alt _ bs rhs) = exprFreeVars rhs `disjointVarSet` mkVarSet bs
    guard $ all unbound alts

    -- Check if all alts are equivalent, modulo free variables. Also returns
    -- this equivalent entry if it exists, as we'll use it later. Note we don't
    -- need to check the variables introduced by the alt as we already checked
    -- that they are unbound!
    let cmp (Alt _ _ rhs) (Alt _ _ rhs') = do
          eqCoreExpr rhs rhs'
    expr <- case nubBy cmp alts of
      [Alt _ _ e] -> pure e
      _ -> empty

    -- Get all free variables in this expression for the in-scope set.
    inScope <- reader inScopeSet

    -- Use the in-scope set to make a substitution for the scrutinee.
    let subst = extendSubst (mkEmptySubst inScope) bind scrut

    -- Perform the substitution.
    pure $ substExpr subst expr

  _ -> empty

-- | Deduplicate case expressions.
--
-- Remove case expressions that scrutinize over the same expression. Note that
-- this does nothing for a nested case in the DEFAULT branch. We merge such
-- nested cases in a separate function. This pass only deduplicates directly
-- adjacent case expressions and thus relies on case reordering to eliminate all
-- duplicates.
-- TODO: We should be merging occurence info in this pass! Both for the case
-- binder as well as the binders of each alternative.
caseDedup :: Alternative m => MonadCore m => MonadReader r m => HasInScopeSet r => Pass m CoreExpr
caseDedup = \case
  Case oScrut oBndr oTy oAlts -> do
    -- We will substitute this value later, so occurence info after this might
    -- not be accurate.
    let oBndr' = clearOccInfo oBndr

    let dedup = \case
          Alt con oBndrs (Case iScrut iBndr _ iAlts) -> do
            -- We will substitute this value later, so occurence info after this
            -- might not be accurate.
            let oBndrs' = clearOccInfo <$> oBndrs

            -- We cannot deduplicate a default case on the outer alt.
            guard $ con /= DEFAULT

            -- Ensure the inner scrutinee doesn't bind variables in the alt, as
            -- it is never equivalent if it does.
            guard $ exprFreeVars iScrut `disjointVarSet` mkVarSet oBndrs'

            -- Check if we bind the same scrutinee. At this point, we already
            -- know there is no shadowing of variables due to the previous
            -- check.
            guard $ eqCoreExpr oScrut iScrut || eqCoreExpr (Var oBndr') iScrut

            -- Find the inner pattern matching the outer constructor.
            Alt _ iBndrs rhs <- maybeM $ findAlt con iAlts

            -- Map all the binders of the case to the expressions along the
            -- spine. Additionally, the binder should be substituted by the
            -- scrutinee.
            let oVars = oBndr' : oBndrs'
            let iVars = iBndr : iBndrs
            let mapping = zip iVars $ Var <$> oVars

            -- Make the substition using the mapping. We make sure to extend the
            -- environment with the new binders from both cases.
            inScope <- reader inScopeSet
            let inScope' = extendInScopeSetList inScope $ oVars <> iVars
            let subst = extendSubstList (mkEmptySubst inScope') mapping

            -- Perform the substitution and return the new alt.
            let rhs' = substExpr subst rhs
            pure $ Alt con oBndrs' rhs'

          _ -> empty

    -- Get the deduplicated alts.
    maybeAlts <- forM oAlts $ runMaybeT . dedup

    -- Return empty if no deduplication happened.
    guard $ any isJust maybeAlts

    -- For any alt where deduplication failed, we use the old expression.
    let oAlts' = uncurry fromMaybe <$> zip oAlts maybeAlts

    -- Return the modified case expression.
    pure $ Case oScrut oBndr' oTy oAlts'

  _ -> empty

-- | Merges nested cases.
--
-- When a case has a DEFAULT pattern, any nested cases over the same scrutinee
-- cannot be deduplicated. As such, we instead merge the two cases. This
-- pass only merges adjacent cases (no deep nesting) and thus relies on case
-- reodering to make the cases adjecent.
caseMerge :: Alternative m => MonadReader r m => HasInScopeSet r => Pass m CoreExpr
caseMerge = \case
  Case oScrut oBind oTy (Alt DEFAULT _ (Case iScrut iBind _ iAlts) : oAlts) -> do
    -- Ensure that the cases scrutinize the same expression.
    guard $ eqCoreExpr oScrut iScrut || eqCoreExpr (Var oBind) iScrut

    -- Substitute the inner case binder.
    inScope <- reader inScopeSet
    let subst = extendSubst (mkEmptySubst inScope) iBind (Var oBind)
    let iAlts' = substAlt subst <$> iAlts

    -- Merge the alternatives. Note that we provide the outer alts first as they
    -- should be prioritised.
    let oAlts' = mergeAlts oAlts iAlts'
    pure $ Case oScrut oBind oTy oAlts'

  _ -> empty

-- | Swap the order of nested cases.
--
-- This function will swap the order of two adjacent cases. It checks whether
-- this is required by definition order of the variables in the scrutinee.
caseSwap
  :: Alternative m
  => MonadCore m
  => MonadReader r m
  => HasCaseBndrs r
  => HasOrderedDecl r
  => HasInScopeSet r
  => Pass m CoreExpr
caseSwap = \case
  Case oScrut oBind oTy oAlts -> do
    -- TODO: I feel like there exists a library function that does this!
    let firstSucceeding f = asum . flip fmap f

    -- Get the unbound alt as an irrefutable pattern.
    (oConSwap, oBndrsSwap, (iScrut, iBndr, iTy, iAlts))
      <- firstSucceeding oAlts $ \case
        Alt con bndrs (Case iScrut iBndr iTy iAlts) -> do
          -- Checks whether the cases are swappable
          guard $ exprFreeVars iScrut `disjointVarSet` mkVarSet bndrs

          -- Checks whether we should reorder the cases, according to some
          -- ordering based on the scrutinees.
          decl <- reader orderedDecl
          let decl' = bndrs <> (oBind : decl)
          cmp <- compareScrut' decl' oScrut iScrut
          guard $ LT == cmp

          -- Irrefutable pattern of the inner case.
          pure (con, bndrs, (iScrut, iBndr, iTy, iAlts))
        _ -> empty

    -- Create substitution with outer case binder.
    inScope <- reader inScopeSet
    let subst0 = mkEmptySubst inScope
    let (subst1, oBind') = substBndr subst0 oBind

    -- For the alternative that will be swapped for the inner binder, we need to
    -- adhere to the ordering of case binders. That is, the outer alternative
    -- binders should be substituted first.
    let (substSwap0, oBndrsSwap') = substBndrs subst1 oBndrsSwap

    -- Substitute a possible case binder in the inner scrutinee.
    let iScrut' = do
          let subst = extendSubst substSwap0 oBind' oScrut
          substExpr subst iScrut

    -- Substitute the inner case binder.
    let (substSwap1, iBndr') = substBndr substSwap0 iBndr

    -- Adjust every inner alternative to contain the outer alternative. Note
    -- that special care is taken whenever we encounter the "swap" alternative
    -- (i.e. the outer alternative that originally contained the inner case).
    iAlts' <- forM iAlts $ \(Alt iCon iBndrs iRhs) -> do
      -- Substitute the inner binders
      let (substSwap2, iBndrs') = substBndrs substSwap1 iBndrs

      -- We return the outer alt as its inner version.
      oAlts' <- forM oAlts $ \case
        -- This is the alternative where the inner case resides. Thus, this is
        -- where the outer case should perform the operation of the inner case.
        Alt oCon _ _ | oCon == oConSwap -> do
          let iRhs' = substExpr substSwap2 iRhs
          pure $ Alt oConSwap oBndrsSwap' iRhs'

        -- This is a non swap-alternative, we only need to ensure binders
        -- are correctly dealt with. The alt can remain as is. We purposely
        -- don't use a substitution with the inner case variables, as these
        -- should have never occurred in this outer branch in the first place.
        -- Substituting these binders would cause variable capturing.
        oAlt -> pure $ substAlt subst1 oAlt

      -- The new inner rhs contain the outer rhs. Use the inner binders as
      -- populated when building the substitution map for the swap case.
      let iRhs' = Case oScrut oBind' oTy oAlts'
      pure $ Alt iCon iBndrs' iRhs'

    pure $ Case iScrut' iBndr' iTy iAlts'

  _ -> empty

-- NOTE: Case Reordering
--
-- Let's first consider swapping binders without the complexity of case
-- expressions.
--
-- :: a -> b -> b
-- \x -> \x -> x
--        |    |
--        +----+
--
-- transform to (handling shadowing correctly)
--
-- :: b -> a -> b
-- \x -> \x -> x
--  |          |
--  +----------+
--
-- I think if we use substBndr in the normal ordering first, we would get
--
-- :: a -> b -> b
-- \x -> y -> y
--
-- Then we can just reorder afterwards:
--
-- :: b -> a -> b
-- \y -> \x -> y
--
-- Which is then alpha equivalent to the above
--
-- So how does this work for nested cases?
--
-- case x of
--   Just a -> case y of
--        |
--        +-------+
--                |
--     Nothing -> a

--     Just a -> a
--          |    |
--          +----+
--
--   Nothing -> a
--              |
--             free
--
-- transform to (handling shadowing correctly)
--
-- case y of
--   Nothing -> case x of
--     Just a -> a
--          |    |
--          +----+
--
--     Nothing -> a
--                |
--               free
--
--   Just a -> case x of
--        |
--        +------+
--               |
--     Just a -> a
--
--     Nothing -> a
--                |
--               free
--
-- My intuition is that for the paths that did not contain the inner case y
-- (i.e. the free a in this example), we should **not** add the binders of
-- the inner case when substituting. How do we unique away the case binders
-- of the inner expression? I guess we can just do it, as the in scope set
-- should make sure we don't pick variables that are free in the other
-- scope no?

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
--
-- TODO: We should order product types before sum types wherever possible.
-- This will reduce the total expression size, while being easy to uphold.
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

compareScrut'
  :: MonadReader r m
  => HasOrderedDecl r
  => HasCaseBndrs r
  => [CoreBndr]
  -> CoreExpr
  -> CoreExpr
  -> m Ordering
compareScrut' bndrs lhs rhs = do
  decl <- (bndrs <>) <$> reader orderedDecl

  -- Finds the index of an id, if it exists
  let idIndex = flip elemIndex decl

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
        (App f a, App f' a') -> cmp f f' <> cmp a a'
        (Cast e _, Cast e' _) -> cmp e e'
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

  wilds <- reader caseBndrs
  let isWild = \case
        Var x -> elemVarSet x wilds
        _ -> False

  pure $ if isWild lhs || isWild rhs then EQ else cmp lhs rhs

