module Transform
  ( deshadowExpr
  , betaReduce
  , caseReduce
  , caseBndrReduce
  , caseDistribute
  , caseMerge
  , caseSwap
  , redundantCase
  , undefaultCase
  , inlineUnfolding
  , dropTick
  , dropReflCast
  , joinCasts
  , floatCast
  , applyBuiltinRule
  , normalize
  , lint
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Map.Expr (eqCoreExpr)
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
import GHC.Core.TyCo.Rep (Coercion (..), Scaled (..))
import GHC.Core.Lint (lintExpr)
import GHC.Core.Rules.Config (RuleOpts(..))
import GHC.Core.Unify (tcMatchTy)
import GHC.Platform (genericPlatform)
import GHC.Driver.Config.Core.Lint (initLintConfig)
import GHC.Tc.Utils.TcType (tcSplitSigmaTy)
import GHC (dataConType)

import Data.Composition ((.:))
import Data.Foldable (foldl', find)
import Data.List (nubBy)
import Data.Maybe (fromMaybe)

import Control.Monad (forM, forM_, guard)
import Control.Monad.Trans.Maybe (runMaybeT)
import Control.Monad.Reader (MonadReader, reader)
import Control.Applicative (Alternative (..), empty, asum)

import Lens.Micro

import Types
import Util
import Unification (matchArgsApp, matchExpr)
import qualified Subst

-- | Substitution over a core expression.
type Substitution m s a = s -> Pass m a

-- | A transformation.
--
-- Given a continuation, a transformation will modify the core expression,
-- after which it will call the given substitution on the (sub-parts) of the
-- new expression.
--
-- The intent is that we can perform multiple transformations in a single
-- sweep over a core expression. We do this by calling the given substitution
-- function in favor of a call to `substExpr`.
--
-- Notice how the given substitution function itself can be a transformation,
-- given that it is a closure of a transformation.
type Transform m s a = Substitution m s a -> Substitution m s a

-- | Initial substitution for the normalization pass.
initSubst :: Subst.Class s => CoreProgram -> s
initSubst = flip Subst.extendProg $ Subst.new emptyInScopeSet

-- | Lint an expression.
--
-- This will panic if the lint fails.
lint
  :: HasCallStack
  => Monad m
  => HasDynFlags m
  => InScopeSet
  -> CoreExpr
  -> m ()
lint (InScope scope) expr = do
  dflags <- getDynFlags
  let vars = nonDetEltsUniqSet scope
  let cfg = initLintConfig dflags vars
  let res = lintExpr cfg expr
  forM_ res $ \message -> do
    -- pprPanic "UC lint error:" $ ppr expr $+$ ppr message
    pprPanic "UC lint error:" $ ppr message

-- TODO: I want a version with and without lint. The lint version should go into
-- the test bench.
normalize
  :: MonadReader r m
  => HasModGuts r
  => HasDynFlags m
  => Pass m CoreExpr
normalize expr = do
  binds <- reader $ mg_binds . modGuts
  let subst = initSubst binds
  loop subst expr

loop
  :: Monad m
  => HasDynFlags m
  => Subst.Ordered
  -> CoreExpr
  -> m CoreExpr
loop subst expr = do
  expr' <- occurAnalyseExpr <$> transform subst expr
  lint (subst ^. Subst.scope) expr'
  -- TODO: We should do CSE (Common Sub-expression Elimination) here for case
  -- binders.
  -- dbg' "========================="
  -- dbg expr'
  -- TODO: We should do better change detection. This can be relatively
  -- expensive.
  if eqCoreExpr expr expr' then pure expr' else loop subst expr'

-- | A full transformation pass.
transform
  :: Monad m
  => Substitution m Subst.Ordered CoreExpr
transform subst expr = do
  let passes = asum $ fmap (\pass -> pass transform subst expr)
        [ betaReduce
        , caseReduce
        , dropTick
        , caseBndrReduce
        , caseMerge
        , caseDistribute
        , dropReflCast
        , joinCasts
        , floatCast
        , inlineUnfolding
        , undefaultCase
        , redundantCase
        , caseSwap
        -- , applyBuiltinRule
        ]

  expr' <- runMaybeT passes
  let def = deshadowExpr transform subst expr
  maybe def pure expr'

-- | Deshadow an expression.
--
-- This substitution will call continue on one nesting in the expression. The
-- intention is that if no transformation happens, this will perform a normal
-- substitution for the current layer and then continue with the transformation.
-- That is, this can be seen as the default operation if no transformation could
-- be made.
deshadowExpr
  :: Monad m
  => Subst.Class s
  => Transform m s CoreExpr
deshadowExpr continue subst = \case
  Var var -> pure $ Subst.lookupId subst var

  Type ty -> do
    let ty' = Subst.ty subst ty
    pure $ Type ty'

  Coercion co -> do
    let co' = Subst.co subst co
    pure $ Coercion co'

  Lit lit -> pure $ Lit lit

  App fun arg -> do
    fun' <- continue subst fun
    arg' <- continue subst arg
    pure $ App fun' arg'

  Tick tickish expr -> do
    let tickish' = Subst.tick subst tickish
    expr' <- continue subst expr
    pure $ mkTick tickish' expr'

  Cast expr co -> do
    expr' <- continue subst expr
    let co' = Subst.co subst co
    pure $ Cast expr' co'

  Lam bndr body -> do
    let (bndr', subst') = subst & Subst.bndr bndr
    body' <- continue subst' body
    pure $ Lam bndr' body'

  Let bind body -> do
    -- TODO: This should do a 'continue' call on the bind no? We should make a
    -- function called deshadowBind! Btw, maybe the deshadow family of functions
    -- should be called transformX instead? I guess it does do deshadowing
    -- at the layer, but it kind of hides the intent as a "if all else fails,
    -- continue like this" function. If not rename, we maybe at least should
    -- go from deshadowX to deShadowX
    (bind', subst') <- deshadowBind continue subst bind
    body' <- continue subst' body
    pure $ Let bind' body'

  Case scrut bndr ty alts -> do
    scrut' <- continue subst scrut
    let ty' = Subst.ty subst ty

    let (bndr', subst') = subst & Subst.bndr bndr

    alts' <- deshadowAlts continue subst' alts

    pure $ Case scrut' bndr' ty' alts'

deshadowBind
  :: Monad m
  => Subst.Class s
  => Substitution m s CoreExpr
  -> s
  -> CoreBind
  -> m (CoreBind, s)
deshadowBind continue subst = \case
  NonRec bndr rhs -> do
    let (bndr', subst') = subst & Subst.bndr bndr
    rhs' <- continue subst' rhs
    pure (NonRec bndr' rhs', subst')

  Rec pairs -> do
    let (bndrs, rhss) = unzip pairs
    let (bndrs', subst') = subst & Subst.recBndrs bndrs
    rhss' <- forM rhss $ continue subst'
    let pairs' = zip bndrs' rhss'
    pure (Rec pairs', subst')

-- | Deshadow multiple alternatives.
--
-- For more information, see `deshadowExpr` and `deshadowAlt`.
deshadowAlts
  :: Monad m
  => Subst.Class s
  => Substitution m s CoreExpr
  -> Substitution m s [CoreAlt]
deshadowAlts = mapM .: deshadowAlt

-- | Deshadow an alternative.
--
-- This will substitute the binders of the expression, after which it will call
-- the remaining substitution on the right-hand-side.
deshadowAlt
  :: Monad m
  => Subst.Class s
  => Substitution m s CoreExpr
  -> Substitution m s CoreAlt
deshadowAlt continue subst (Alt con bndrs rhs) = do
  let (bndrs', subst') = subst & Subst.bndrs bndrs
  rhs' <- continue subst' rhs
  pure $ Alt con bndrs' rhs'

-- | Inlines all non-typeclass functions.
inlineUnfolding
  :: Alternative m
  => Transform m s CoreExpr
inlineUnfolding _ _ = \case
  Var var -> case idUnfolding var of
    CoreUnfolding { uf_tmpl } -> pure uf_tmpl

    DFunUnfolding { df_bndrs, df_con, df_args } -> do
      let con = Var $ dataConWorkId df_con
      let inner = foldl App con df_args
      let quantified = foldr Lam inner df_bndrs
      pure quantified

    _ -> empty

  _ -> empty

-- | Apply builtin rewrites.
--
-- Applies builtin rewrites for variables. This will produce plenty of case
-- expressions, so use with caution.
--
-- TODO: Maybe I should pick a subset of rules to apply. Unfolding equals is for
-- example a lot less interesting than unfolding a fromInteger on a constant.
applyBuiltinRule
  :: Alternative m
  => Monad m
  => Subst.Class s
  => Transform m s CoreExpr
applyBuiltinRule continue subst expr = do
  let (spine, args) = collectArgs expr
  spine' <- case spine of
    Var var | isId var -> pure var
    _ -> empty

  asum $ idCoreRules spine' <&> \case
    Rule {} -> empty
    BuiltinRule { ru_nargs, ru_try } -> do
      guard $ ru_nargs == length args
      let opts = RuleOpts
            { roPlatform = genericPlatform
            , roNumConstantFolding = True
            , roExcessRationalPrecision = False
            , roBignumRules = False
            }
      let scope = ISE (subst ^. Subst.scope) noUnfoldingFun
      expr' <- maybeM $ ru_try opts scope spine' args
      continue subst expr'

-- | Beta reduction
betaReduce
  :: Monad m
  => Alternative m
  => Subst.Class s
  => Transform m s CoreExpr
betaReduce continue subst = \case
  -- Normal beta reduction.
  App (Lam bndr body) arg -> substitute body bndr arg

  -- Reduction on let binding.
  Let (NonRec bndr expr) body -> substitute body bndr expr

  _ -> empty
  where
    substitute body bndr expr = do
      expr' <- continue subst expr
      let subst' = subst & Subst.extend bndr expr'
      continue subst' body

-- | Reduces a case expression if the spine of the scrutinee is a constructor.
caseReduce
  :: Alternative m
  => Monad m
  => Subst.Class s
  => Transform m s CoreExpr
caseReduce continue subst = \case
  Case scrut bndr _ alts -> do
    -- Get the spine and its arguments
    let (spine, args) = collectArgs scrut

    -- Notice how we first get the constructor before substituting the
    -- scrutinee. This is to ensure we don't throw away this part of the
    -- computation, which would happen if we first substitute and then check if
    -- there is a constructor afterwards.
    (con, tyVars, exArgs) <- case spine of
      Var v -> do
        -- Similar to `trimConArgs`, but retains the type variables.
        con <- maybeM $ isDataConId_maybe v
        let idx = length $ dataConUnivTyVars con
        let (tyVars, exArgs) = splitAt idx args
        pure (DataAlt con, tyVars, exArgs)

      Lit l -> do
        guard $ null args
        pure (LitAlt l, [], [])

      _ -> empty

    -- Get the alt matching this spine. This should never fail.
    Alt _ bndrs rhs <- maybeM $ findAlt con alts

    -- Substitute the arguments of the spine.
    tyVars' <- forM tyVars $ continue subst
    exArgs' <- forM exArgs $ continue subst
    spine' <- continue subst spine

    -- Reconstruct the scrutinee.
    let scrut' = foldl' App spine' $ tyVars' <> exArgs'

    -- Make the substitution map using the substituted arguments (not the types)
    -- and the full scrutinee.
    let mapping = (bndr, scrut') : zip bndrs exArgs'
    let subst' = subst & Subst.extendMany mapping

    -- We can continue substitution on the entire right-hand-side.
    continue subst' rhs

  _ -> empty

-- | Distrubte expressions over a case.
--
-- This pushes case expressions towards the root of the expression.
caseDistribute
  :: Alternative m
  => Monad m
  => Subst.Class s
  => Transform m s CoreExpr
caseDistribute continue subst = \case
  -- Nested case
  Case scrut@Case {} bndr ty alts -> do
    let ty' = Subst.ty subst ty
    let (bndr', subst') = subst & Subst.bndr bndr
    alts' <- deshadowAlts continue subst' alts

    distribute (\rhs -> Case rhs bndr' ty' alts') continue subst scrut

  -- Inline argument into case
  fun@(Case _ _ ty _) -> do
    -- Split this case if it is a function.
    (_, mult, argTy, _) <- maybeM $ splitFunTy_maybe ty

    -- Create a fresh variable to distribute.
    let argTy' = Scaled mult $ Subst.ty subst argTy
    let (fresh, subst') = subst & Subst.scope %~~ freshId "distributed" argTy'

    -- Distribute the variable and place it as an abstraction outside of the
    -- lambda.
    expr <- distribute (`App` Var fresh) continue subst' fun
    pure $ Lam fresh expr

  -- Inline function into case
  App fun arg@Case {} -> do
    fun' <- continue subst fun
    distribute (fun' `App`) continue subst arg

  -- Inline cast into case
  Cast expr@Case {} co -> do
    let co' = Subst.co subst co
    distribute (`Cast` co') continue subst expr

  _ -> empty

-- | Distributes a map over a case expression.
--
-- This will ensure correct variable capturing, given that the substitution map
-- includes all variables bound by the result of the mapping function. Note that
-- the mapping function is not expected to substitute the right-hand-side; this
-- already happens prior to the map using the given substitution.
distribute
  :: Alternative m
  => Monad m
  => Subst.Class s
  => (CoreExpr -> CoreExpr)
  -> Transform m s CoreExpr
distribute adjust continue subst = \case
  Case scrut bndr _ alts -> do
    -- Continue on the scrutinee.
    scrut' <- continue subst scrut

    -- First deshadow the alternatives like normal.
    let (bndr', subst') = subst & Subst.bndr bndr
    alts' <- deshadowAlts continue subst' alts

    -- Since all binders in the alts are now non-clashing with previously
    -- defined binders, we can call our helper function that actually
    -- distributes without worrying about variable capturing.
    let alts'' = alts' <&> \(Alt con bndrs rhs) -> do
          Alt con bndrs $ adjust rhs

    -- Get the type of the new alternatives.
    let ty' = coreAltsType alts''

    -- Return the new case expression, with adjusted alts.
    pure $ Case scrut' bndr' ty' alts''

  _ -> empty

-- | Removes obselete cases.
--
-- That is, cases whose result will not change depending on the value of the
-- scrutinee.
redundantCase
  :: Alternative m
  => Monad m
  => Subst.Class s
  => Transform m s CoreExpr
redundantCase continue subst = \case
  Case scrut bind _ alts -> do
    -- Check if all alts do not bind any of their pattern (which would make
    -- them not equivalent due to different binding variables).
    let unbound (Alt _ bs _) = all isDeadBinder bs
    guard $ all unbound alts

    -- Check if all alts are equivalent, modulo free variables. Also returns
    -- this equivalent entry if it exists, as we'll use it later. Note we don't
    -- need to check the variables introduced by the alt as we already checked
    -- that they are unbound!
    let cmp (Alt _ _ rhs) (Alt _ _ rhs') = eqCoreExpr rhs rhs'
    expr <- case nubBy cmp alts of
      [Alt _ _ e] -> pure e
      _ -> empty

    -- We substitute the case binder in the new expression.
    let subst' = subst & Subst.extend bind scrut
    continue subst' expr

  _ -> empty

-- | Reduces any occurence of a case binder to the alt of that branch.
--
-- When we inline the case binder in this way, we can actually reduce duplicate
-- case expressions that are nested.
caseBndrReduce
  :: Alternative m
  => Monad m
  => Subst.Class s
  => Transform m s CoreExpr
caseBndrReduce continue subst = \case
  Case scrut bndr ty alts -> do
    guard . not $ isDeadBinder bndr

    -- Substitute the scrutinee and type like normal.
    scrut' <- continue subst scrut
    let ty' = Subst.ty subst ty

    -- Substitute the case binder like normal
    let (bndr', subst') = subst & Subst.bndr bndr

    -- For every alt, substitute the case binder by the alt constructor if
    -- possible.
    alts' <- forM alts $ \(Alt con bndrs rhs) -> do
      -- Substitute the binders, zapping the occurence info.
      let (bndrs', subst'') = subst' & Subst.bndrs (fmap zapIdOccInfo bndrs)

      -- Create a substitution map where the case binder will be replaced by an
      -- expression representing the alt, if possible.
      let subst''' = fromMaybe subst'' $ do
            -- Create an expression from the alt
            let scope = subst'' ^. Subst.scope
            expr <- altConToExpr scope con bndrs'

            -- Ensure the type matches that of the case binder.
            expr' <- matchExpr scope expr $ varType bndr'
            pure $ subst'' & Subst.extend bndr expr'

      -- Substitute the rhs
      rhs' <- continue subst''' rhs
      pure $ Alt con bndrs' rhs'

    -- FIXME: For default branches, we actually would still need the case
    -- binder, so it is not always dead after this pass. How would we know when
    -- not to do this pass? For numeric altcons for example, we cannot get rid
    -- of default branches.
    -- Set the binder as dead, such that we do not repeat this pass!
    let bndr'' = setIdOccInfo bndr' IAmDead

    -- Return the modifier case expression.
    pure $ Case scrut' bndr'' ty' alts'

  _ -> empty

-- | Transform an alt con with binders to an expression.
altConToExpr
  :: Alternative m
  => Monad m
  => InScopeSet
  -> AltCon
  -> [CoreBndr]
  -> m CoreExpr
altConToExpr scope con bndrs = case con of
  DataAlt dataCon -> dataConToExpr scope dataCon bndrs

  LitAlt lit -> do
    guard $ null bndrs
    pure $ Lit lit

  DEFAULT -> empty

-- | Transform a data con with binders to an expression.
dataConToExpr
  :: Alternative m
  => Monad m
  => InScopeSet
  -> DataCon
  -> [CoreBndr]
  -> m CoreExpr
dataConToExpr scope con bndrs = do
  -- Create an expression of the data con with blank type variables.
  let spine = Var $ dataConWorkId con
  let tyVars = Type . mkTyVarTy <$> dataConUnivTyVars con
  let untyped = mkApps spine tyVars

  -- Now match the blank type variable to the binders.
  let bndrs' = Var <$> bndrs
  matchArgsApp scope untyped bndrs'

-- | Removes the default alternative in case statements.
--
-- This only works for data constructors, as these have a finite number of
-- patterns, unlike for example numeric literals.
undefaultCase
  :: Alternative m
  => Monad m
  => Subst.Class s
  => Transform m s CoreExpr
undefaultCase continue subst = \case
  Case scrut bndr ty alts -> do
    -- Get the default value and remaining alts. We return empty if there
    -- doesn't exist a default branch.
    (explicit, rhsDefault) <- do
      let (explicit, def) = findDefault alts
      def' <- maybeM def
      pure (explicit, def')

    -- Get the dataconstructors for this scrutinee. Note that we only remove
    -- default cases for data constructors. That is, we cannot really do this
    -- in the same way for types with infinite constructors such as literals.
    dataCons <- maybeM $ do
      (tyCon, _) <- tcSplitTyConApp_maybe $ varType bndr
      tyConDataCons_maybe tyCon

    -- Fetches the alt corresponding to the given constructor, if it exists.
    let originalAlt dataCon = do
          let cmp (Alt con _ _) = DataAlt dataCon == con
          maybeM $ find cmp explicit

    -- Create an explicit alt using the default rhs.
    let explicitDefault dataCon = do
          -- Get binders with types matching the scrutinee/case binder, this
          -- should never fail if you provide a matching bndr dataCon pair.
          let scope = subst ^. Subst.scope
          (bndrs, _) <- freshAltBndrs scope bndr dataCon

          -- Create the default binder with explicit constructor and binders.
          let con = DataAlt dataCon
          let bndrs' = bndrs <&> (`setIdOccInfo` IAmDead)
          pure $ Alt con bndrs' rhsDefault

    -- Create the new alternatives. Note that they should be ordered in the same
    -- way as the its list of data constructors. For this reason, we first try
    -- to get the original alternative, before constructing the explicit default
    -- case. In the end, all alts are now explicit.
    alts' <- forM dataCons $ originalAlt <|-|> explicitDefault

    -- Since we only added some fresh (dead) binders to the alts, it is safe to
    -- continue on the entire expression.
    continue subst $ Case scrut bndr ty alts'

  _ -> empty

-- | Create a set of fresh binders for an alt, if possible.
--
-- The current in-scope set and case binder is passed along. The case binder is
-- added to the in-scope set for fresh variable generation. Additionally, the
-- binders will by typed such that they would match the type of the case binder
-- if they're used in an alternative.
--
-- This fails if the data constructor cannot be matched to the core binder type.
freshAltBndrs
  :: Alternative m
  => Monad m
  => InScopeSet
  -> CoreBndr
  -> DataCon
  -> m ([CoreBndr], InScopeSet)
freshAltBndrs scope bndr dataCon = do
  let scope' = extendInScopeSet scope bndr
  let goalTy = varType bndr

  -- Get the base types for the arguments and result of the constructor.
  let (_, _, funTy) = tcSplitSigmaTy $ dataConType dataCon
  let (argTys, resTy) = splitFunTys funTy

  -- We try to match the result type of the constructor to the case binder.
  -- Really, this should never fail.
  subst <- maybeM $ tcMatchTy resTy goalTy
  let argTys' = substScaledTy subst <$> argTys

  -- Now we construct the case binders, with the correct types.
  let ids = argTys' <&> ("unused",)
  pure $ freshIds ids scope'

-- | Merges nested cases.
--
-- When a case has a DEFAULT pattern, any nested cases over the same scrutinee
-- cannot be deduplicated. As such, we instead merge the two cases. This
-- pass only merges adjacent cases (no deep nesting) and thus relies on case
-- reodering to make the cases adjecent.
caseMerge
  :: Alternative m
  => Monad m
  => Subst.Class s
  => Transform m s CoreExpr
caseMerge continue subst = \case
  Case oScrut oBndr oTy (Alt DEFAULT _ (Case iScrut iBndr _ iAlts) : oAlts) -> do
    -- Ensure that the cases scrutinize the same expression.
    guard $ eqCoreExpr (Var oBndr) iScrut || eqCoreExpr oScrut iScrut

    -- Continue on the outer alts.
    oAlts' <- deshadowAlts continue subst oAlts

    -- Continue on the inner alts, substituting the case binder.
    let subst' = subst & Subst.extend iBndr (Var oBndr)
    iAlts' <- deshadowAlts continue subst' iAlts

    -- Merge the alternatives. Note that we provide the outer alts first as they
    -- should be prioritised. We purposely leave out the default case in this
    -- merge. Otherwise, it would be a no-op.
    let oAlts'' = mergeAlts oAlts' iAlts'
    pure $ Case oScrut oBndr oTy oAlts''

  _ -> empty

-- TODO: Implement the case reordering
-- More detailed:
-- I want to order based on the uniques of binders. The thing is that they're
-- not guaranteed stable. The way local uniques are assigned is by finding
-- the next identifier. Thus if we're smart about the way we introduce local
-- uniques are assigned, we can let the unique reflect the declaration order of
-- variables. Then ordering based on uniques is equivalent to ordering based on
-- declaration order.
--
-- How:
-- There are two things we should do in order to ensure our declaration order
-- property is maintained.
-- 1. When we start the normalisation, we want the uniques to be in declaration
--    order.
-- 2. Any transformation should maintain declaration order.
--
-- The first step is rather simple. We can just make a pass that performs
-- substBndr, but then always fetches the next unique.
--
-- The second step might be a bit more difficult. I guess we could also use this
-- new substBndr that fetches the next unique? Otherwise, I'm worried there will
-- be holes, such that later invokations of the old substBndr gets a unique from
-- such a hole. An example where a hole would occur would be in a beta reduction.
--
-- The problem with doing this would be that it causes a lot more substitutions.
-- I'm slightly worried about performance with this approach, but maybe it's
-- not so bad? Fetching the new unique would be somewhat quick no? The annoying
-- thing is that this would influence the other passes in a non-trivial way;
-- they would all need to use different set of substitution functions.
-- 
-- The alternative would be to track the ordering in a list or such. I would be
-- completely fine with this if I could restrict it to this pass and perhaps the
-- transform function. That would require a lot less adjustments, but then I
-- don't think that this is really possible either. At least not without again
-- adjusting the functions that see all declarations (i.e. substBndr et al).
--
-- Though maybe, it is a lot advisable to just track the ordering in a list via
-- a modified substBndr than to adjust the whole scheme of in which uniques are
-- assigned? Even if it gets a bit more messy...
--
-- Hmm. Actually, it seems the local uniques are just fetched via a counter. It
-- will not attempt to find empty slots. With this in mind, probably we can
-- uphold our invariant with the normal substBndr. Then we only need to do step
-- 1. I'm pretty sure the other passes always create binders in declaration
-- order. I think in fact this is required in order to avoid capturing. My
-- guess is that we can simply perform step 1 and that the invariant is held
-- afterwards.
--
-- Wait. The problem is not with finding new binders. It's with old binders that
-- actually do not conflict with the in-scope set. For any of such binders, we
-- will actually not call uniqAway, and thus risk ruining declaration order.
-- The funny thing is that a modification to substBndr that always would call
-- uniqAway would probably be enough. In the end, it's not so clear. Let's
-- come back to this!
--
-- It think adjusting the substBndr et al would work. I also think it is a very
-- invisible invariant, that highly depends on an implementation detail of the
-- unique binder generation of haskell. In that sense, perhaps we should make
-- our own subst type. Maybe even a typeclass for it, such that we can use the
-- normal GHC version or any adjusted one.
caseSwap
  :: Alternative m
  => Monad m
  => Transform m Subst.Ordered CoreExpr
caseSwap continue subst = \case
  Case oScrut oBind oTy oAlts -> do
    -- Get the unbound alt as an irrefutable pattern.
    (oConSwap, oBndrsSwap, (iScrut, iBndr, iTy, iAlts)) <- asum $ oAlts <&> \case
      Alt con bndrs (Case iScrut iBndr iTy iAlts) -> do
        -- Checks whether the cases are swappable
        guard $ exprFreeVars iScrut `disjointVarSet` mkVarSet bndrs

        -- Checks whether we should reorder the cases, according to some
        -- ordering based on the scrutinees.
        guard $ LT == compareScrut subst oScrut iScrut

        -- Irrefutable pattern of the inner case.
        pure (con, bndrs, (iScrut, iBndr, iTy, iAlts))
      _ -> empty

    oScrut' <- continue subst oScrut
    let oTy' = Subst.ty subst oTy
    let (oBind', subst') = subst & Subst.bndr oBind

    -- For the alternative that will be swapped for the inner binder, we need to
    -- adhere to the ordering of case binders. That is, the outer alternative
    -- binders should be substituted first.
    let (oBndrsSwap', substSwap) = subst' & Subst.bndrs oBndrsSwap

    -- Get the new inner scrutinee and type.
    iScrut' <- continue substSwap iScrut
    let iTy' = Subst.ty substSwap iTy

    -- Substitute the inner case binder.
    let (iBndr', substSwap') = substSwap & Subst.bndr iBndr

    -- Adjust every inner alternative to contain the outer alternative. Note
    -- that special care is taken whenever we encounter the "swap" alternative
    -- (i.e. the outer alternative that originally contained the inner case).
    iAlts' <- forM iAlts $ \(Alt iCon iBndrs iRhs) -> do
      -- Substitute the inner binders
      let (iBndrs', substSwap'') = substSwap' & Subst.bndrs iBndrs

      -- We return the outer alt as its inner version.
      oAlts' <- forM oAlts $ \case
        -- This is the alternative where the inner case resides. Thus, this is
        -- where the outer case should perform the operation of the inner case.
        Alt oCon _ _ | oCon == oConSwap -> do
          iRhs' <- continue substSwap'' iRhs
          pure $ Alt oConSwap oBndrsSwap' iRhs'

        -- This is a non swap-alternative, we only need to ensure binders
        -- are correctly dealt with. The alt can remain as is. We purposely
        -- don't use a substitution with the inner case variables, as these
        -- should have never occurred in this outer branch in the first place.
        -- Substituting these binders would cause variable capturing.
        oAlt -> deshadowAlt continue subst' oAlt

      -- The new inner rhs contain the outer rhs. Use the inner binders as
      -- populated when building the substitution map for the swap case.
      let iRhs' = Case oScrut' oBind' oTy' oAlts'
      pure $ Alt iCon iBndrs' iRhs'

    pure $ Case iScrut' iBndr' iTy' iAlts'

  _ -> empty

-- | Compares scrutinees.
--
-- Note that we only expect to swap scrutinees that are normalized (i.e. only
-- contain applications, variables and literals. Any other expression will get
-- an equality, as we don't want to swap them (yet). We compare scrutinees
-- based on declaration ordering.
--
-- FIXME: I think this ordering doesn't really work for normalisation. It
-- might be better to consider what is the 'lowest' variable in an expression,
-- if this is equal, 'second lowest' etc. If all of this is equalt, then we
-- should consider their order of appearance in the expression.
--
-- To be explicit; the total ordering should respect that some cases cannot
-- be reordered (i.e. because the outer binds variables used in the inner
-- scrutinee). The current comparison doesn't respect this property! Hopefully
-- this proposed solution does.
compareScrut
  :: Subst.Ordered
  -> CoreExpr
  -> CoreExpr
  -> Ordering
compareScrut subst lhs rhs = case (lhs, rhs) of
  (Var x, Var y) -> Subst.compareVar subst x y
  (Var _, _) -> GT
  (_, Var _) -> LT
  (Lit x, Lit y) -> compare x y
  (Lit _, _) -> GT
  (_, Lit _) -> LT
  (App f a, App f' a') -> compareScrut subst f f' <> compareScrut subst a a'
  (Cast e _, Cast e' _) -> compareScrut subst e e'
  _ -> EQ

-- | Remove ticks from the expression.
dropTick
  :: Alternative m
  => Transform m s CoreExpr
dropTick continue subst = \case
  Tick _ expr -> continue subst expr

  _ -> empty

-- | Remove reflexive casts.
--
-- Reflexive casts are essentially no-ops.
dropReflCast
  :: Alternative m
  => Transform m s CoreExpr
dropReflCast continue subst = \case
  Cast expr co | isReflexiveCo co -> continue subst expr

  _ -> empty

-- | Join two consecutive casts.
--
-- Merging casts is good both for normalisation and potentially eliminating
-- casts that become reflective by this operation.
joinCasts
  :: Alternative m
  => Transform m s CoreExpr
joinCasts continue subst = \case
  Cast (Cast expr co) co' -> do
    let co'' = mkTransCo co co'
    let expr' = Cast expr co''
    continue subst expr'

  _ -> empty

-- | Float casts over applications.
--
-- This allows more reductions to be able to take place.
floatCast
  :: Alternative m
  => Monad m
  => Subst.Class s
  => Transform m s CoreExpr
floatCast continue subst = \case
  App (Cast fun FunCo { fco_arg, fco_res }) arg -> do
    let arg' = Cast arg fco_arg
    let expr = Cast (App fun arg') fco_res
    continue subst expr

  App (Cast fun (ForAllCo bndr argCo resCo)) (Type arg) -> do
    -- The forall binder should only be substituted within the coercions. As
    -- there is no correct substitution for the entire returned expression, we
    -- continue only on the function body.
    fun' <- continue subst fun
    let arg' = Subst.ty subst arg

    -- Substitute the coercions
    let subst' = subst & Subst.extend bndr (Type arg')
    let argCo' = Subst.co subst' argCo
    let resCo' = Subst.co subst' resCo

    -- Create the new type argument.
    let arg'' = Type $ mkCastTy arg' argCo'

    -- Return the floated cast.
    pure $ Cast (App fun' arg'') resCo'

  _ -> empty

