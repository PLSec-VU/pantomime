module Transform
  ( deShadowExpr
  , betaReduce
  , caseReduce
  , caseBndrReduce
  , caseDistribute
  -- , caseMerge
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
  , substitute
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Map.Expr (eqCoreExpr, CoreMap)
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.TyCo.Rep (Coercion (..), Scaled (..))
import GHC.Core.Rules.Config (RuleOpts(..))
import GHC.Core.Unify (tcMatchTy)
import GHC.Data.TrieMap (insertTM, TrieMap (..))
import GHC.Platform (genericPlatform)
import GHC.Tc.Utils.TcType (tcSplitSigmaTy)
import GHC (dataConType)

import Data.Composition ((.:))
import Data.Foldable (foldl', find)
import Data.Function (fix)
import Data.List (nubBy, sortBy)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, isNothing, fromJust)
import Data.Data (gmapT)
import Data.Generics.Aliases (mkT)

import Control.Monad (forM, guard)
import Control.Monad.Trans.Maybe (runMaybeT)
import Control.Monad.Reader (MonadReader, reader)
import Control.Monad.Trans.Class (MonadTrans (..))
import Control.Applicative (Alternative (..), empty, asum)

import Lens.Micro

import Types
import Util
import Unification (matchArgsApp, matchExpr)
import qualified Subst
import qualified Lint

-- import qualified Debug.Trace as Debug

-- dbg :: Applicative m => Outputable o => o -> m ()
-- dbg m = Debug.trace (showSDocUnsafe $ ppr m) $ pure ()

-- dbg' :: Applicative m => Show o => o -> m ()
-- dbg' m = Debug.trace (show m) $ pure ()

-- | Substitution over some expression.
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
-- Notice how the given transformation function itself can be a substitution,
-- given that it is a closure of a transformation.
type Transform m s a = Substitution m s a -> Substitution m s a

-- | Initial substitution for the normalization pass.
initSubst :: Subst.Class s => CoreProgram -> s
initSubst prog = do
  let scope = mkInScopeSetBndrs prog
  Subst.new scope & Subst.extendProg prog

-- TODO: I want a version with and without lint. The lint version should go into
-- the test bench.
normalize
  :: HasCallStack
  => MonadReader r m
  => HasModGuts r
  => HasDynFlags m
  => Pass m CoreExpr
normalize expr = do
  binds <- reader $ mg_binds . modGuts
  let subst = initSubst binds
  loop subst expr

loop
  :: HasCallStack
  => Monad m
  => HasDynFlags m
  => Subst.Ordered
  -> CoreExpr
  -> m CoreExpr
loop subst expr = do
  let scope = subst ^. Subst.scope
  let extra = occurAnalyseExpr . prepCaseDedup' scope . scrutCSE'
  expr' <- extra <$> linted subst expr
  Lint.panic Lint.full scope expr'

  -- TODO: We should do better change detection. This can be relatively
  -- expensive.
  if eqCoreExpr expr expr' then pure expr' else loop subst expr'

-- | A substitution function from the full transformation.
substitute
  :: HasCallStack
  => Monad m
  => Substitution m Subst.Ordered CoreExpr
substitute = fix transform

-- | A substitution function from the full transformation.
--
-- Additionally, this will lint at every substage to check correctness of the
-- transformations. The intent is to use this solely for debugging.
--
-- TODO: Ideally we pass a flag to the plugin to do linting or not. I want this
-- check as top-level as possible; no `when` at every iteration!
linted
  :: HasCallStack
  => Monad m
  => HasDynFlags m
  => Substitution m Subst.Ordered CoreExpr
linted subst expr = do
  expr' <- transform linted subst expr

  let scope = subst ^. Subst.scope
  Lint.panic Lint.subterm scope expr'
  pure expr'

-- | A full transformation.
--
-- This combines all the passes in a single, non-failible transformation pass.
-- One can recursively apply this transformation to itself to get a full
-- substitution.
transform
  :: HasCallStack
  => Monad m
  => Transform m Subst.Ordered CoreExpr
transform continue subst expr = do
  let passes = asum $ (\pass -> pass (lift .: continue) subst expr) <$>
        [ betaReduce
        , caseReduce
        , caseSelectDefault
        , dropTick
        -- , caseMerge
        , caseDistribute
        , dropReflCast
        , joinCasts
        , floatCast
        , inlineUnfolding
        , undefaultCase
        , redundantCase
        , caseSwap
        , applyBuiltinRule
        , testBuiltinRule
        , caseBndrReduce
        ]

  expr' <- runMaybeT passes
  let def = deShadowExpr continue subst expr
  maybe def pure expr'

-- | Deshadow an expression.
--
-- This substitution will call continue on one nesting in the expression. The
-- intention is that if no transformation happens, this will perform a normal
-- substitution for the current layer and then continue with the transformation.
-- That is, this can be seen as the default operation if no transformation could
-- be made.
--
-- TODO: Btw, maybe the deshadow family of functions should be called
-- transformX instead? I guess it does do deshadowing at the layer, but it
-- kind of hides the intent as a "if all else fails, continue like this"
-- function.
deShadowExpr
  :: HasCallStack
  => Monad m
  => Subst.Class s
  => Transform m s CoreExpr
deShadowExpr continue subst = \case
  Var var -> do
    -- TODO: This empty substitions fixes shadowing for substitions. Not sure if
    -- we want to keep it though. For now, we can keep it to debug! I guess we
    -- could even call continue, given that we check whether we actually found
    -- a substitution. That is, the recursion should somehow stop and the way
    -- to do this would be by checking whether a substitution exists.
    let expr = Subst.lookupId subst var
    let subst' = mkEmptySubst $ subst ^. Subst.scope
    pure $ substExpr subst' expr

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
    (bind', subst') <- deShadowBind continue subst bind
    body' <- continue subst' body
    pure $ Let bind' body'

  Case scrut bndr ty alts -> do
    scrut' <- continue subst scrut
    let ty' = Subst.ty subst ty

    let (bndr', subst') = subst & Subst.bndr bndr
    alts' <- deShadowAlts continue subst' alts

    pure $ Case scrut' bndr' ty' alts'

deShadowBind
  :: Monad m
  => Subst.Class s
  => Substitution m s CoreExpr
  -> s
  -> CoreBind
  -> m (CoreBind, s)
deShadowBind continue subst = \case
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
deShadowAlts
  :: Monad m
  => Subst.Class s
  => Substitution m s CoreExpr
  -> Substitution m s [CoreAlt]
deShadowAlts = mapM .: deShadowAlt

-- | Deshadow an alternative.
--
-- This will substitute the binders of the expression, after which it will call
-- the remaining substitution on the right-hand-side.
deShadowAlt
  :: Monad m
  => Subst.Class s
  => Substitution m s CoreExpr
  -> Substitution m s CoreAlt
deShadowAlt continue subst (Alt con bndrs rhs) = do
  let (bndrs', subst') = subst & Subst.bndrs bndrs
  rhs' <- continue subst' rhs
  pure $ Alt con bndrs' rhs'

-- | Inlines all non-typeclass functions.
--
-- TODO: I think to correctly de-shadow, we should either do an empty substition
-- or a transformation on the unfolding. This of course assumes that the
-- unfolding is not fragile, as this will would make it so we only want to do
-- the empty substition.
inlineUnfolding
  :: Alternative m
  => Monad m
  => Transform m s CoreExpr
inlineUnfolding continue subst = \case
  Var var -> do
    expr <- case idUnfolding var of
      CoreUnfolding { uf_tmpl } -> do
        pure uf_tmpl

      DFunUnfolding { df_bndrs, df_con, df_args } -> do
        let con = Var $ dataConWorkId df_con
        let inner = foldl App con df_args
        let quantified = foldr Lam inner df_bndrs
        pure quantified

      _ -> empty

    continue subst expr

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
    Var var | isPrimOpId var -> pure var
    _ -> empty

  -- Apply the first rule that works.
  expr' <- asum $ idCoreRules spine' <&> \case
    Rule {} -> empty
    BuiltinRule { ru_nargs, ru_try } -> do
      let opts = RuleOpts
            { roPlatform = genericPlatform
            , roNumConstantFolding = True
            , roExcessRationalPrecision = True
            , roBignumRules = True
            }

      -- Apply the built-in rule.
      -- TODO: Should we pick some unfolding fun?
      let scope = ISE (subst ^. Subst.scope) idUnfolding
      expr' <- maybeM $ ru_try opts scope spine' args

      -- Apply the remaining arguments and continue.
      let remaining = drop ru_nargs args
      pure $ mkApps expr' remaining

  continue subst expr'

testBuiltinRule
  :: Alternative m
  => Monad m
  => Subst.Class s
  => Transform m s CoreExpr
testBuiltinRule continue subst expr = do
  let (spine, args) = collectArgs expr
  spine' <- case spine of
    Var var | isPrimOpId var -> pure var
    _ -> empty

  -- Apply the first rule that works.
  expr' <- asum $ idCoreRules spine' <&> \case
    Rule {} -> empty
    BuiltinRule { ru_nargs, ru_try } -> do
      let opts = RuleOpts
            { roPlatform = genericPlatform
            , roNumConstantFolding = True
            , roExcessRationalPrecision = True
            , roBignumRules = True
            }

      -- Apply the built-in rule.
      -- TODO: Should we pick some unfolding fun?
      let scope = ISE (subst ^. Subst.scope) idUnfolding
      expr' <- maybeM $ ru_try opts scope spine' args

      -- Apply the remaining arguments and continue.
      let remaining = drop ru_nargs args
      pure $ mkApps expr' remaining

  continue subst expr'

-- | Beta reduction.
betaReduce
  :: Monad m
  => Alternative m
  => Subst.Class s
  => Transform m s CoreExpr
betaReduce continue subst = \case
  -- Normal beta reduction.
  App (Lam bndr body) arg -> reduce body bndr arg

  -- Reduction on let binding.
  Let (NonRec bndr expr) body -> reduce body bndr expr

  _ -> empty
  where
    reduce body bndr expr = do
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
        dataCon <- maybeM $ isDataConId_maybe v
        let idx = length $ dataConUnivTyVars dataCon
        let (tyVars, exArgs) = splitAt idx args
        pure (DataAlt dataCon, tyVars, exArgs)

      Lit l -> do
        guard $ null args
        pure (LitAlt l, [], [])

      _ -> empty

    -- Substitute the scrutinee in parts.
    spine' <- continue subst spine
    tyVars' <- forM tyVars $ continue subst
    exArgs' <- forM exArgs $ continue subst

    -- Reconstruct the scrutinee.
    let scrut' = foldl' App spine' $ tyVars' <> exArgs'

    -- Get the alt matching this spine. This should never fail.
    Alt _ bndrs rhs <- maybeM $ findAlt con alts

    -- Make the substitution map using the substituted expression arguments (not
    -- the type arguments) and the full scrutinee.
    let mapping = (bndr, scrut') : zip bndrs exArgs'
    let subst' = subst & Subst.extendMany mapping

    -- We can continue substitution on the entire right-hand-side.
    continue subst' rhs

  _ -> empty

-- | Select the default case if no other construct can possible match.
--
-- This will use the OtherCon unfolding to determine whether it is okay to
-- inline the default case.
caseSelectDefault
  :: Alternative m
  => Monad m
  => Subst.Class s
  => Transform m s CoreExpr
caseSelectDefault continue subst = \case
  Case (Var scrut) bndr _ alts -> do
    -- We lookup the scrutinee to see if it has an OtherCon unfolding. Note
    -- we don't call `continue` on the scrutinee here as it might incur a lot
    -- of work for an operation that may fail. Instead, we just do this limited
    -- lookup.
    scrut' <- case Subst.lookupId subst scrut of
      Var scrut' -> pure scrut'
      _ -> empty

    -- Get the default and explicit alternatives, if possible.
    (explicit, rhsDefault) <- do
      let (explicit, def) = findDefault alts
      def' <- maybeM def
      pure (explicit, def')

    -- Check that none of the alternative match the scrutinee.
    let others = Set.fromList . otherCons . idUnfolding $ scrut'
    let noScrutMatch (Alt con _ _) = con `elem` others
    guard $ all noScrutMatch explicit

    -- We just return the default right hand side, since we know for certain
    -- that none of the other alternatives will match.
    let subst' = subst & Subst.extend bndr (Var scrut')
    continue subst' rhsDefault

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
    distribute' subst scrut $ \subst' rhs -> do
      let ty' = Subst.ty subst' ty
      let (bndr', subst'') = subst' & Subst.bndr bndr
      alts' <- deShadowAlts continue subst'' alts
      pure $ Case rhs bndr' ty' alts'

  -- Inline argument into case
  fun@(Case _ _ ty _) -> do
    -- Split this case if it is a function.
    (_, mult, argTy, _) <- maybeM $ splitFunTy_maybe ty

    -- Create a fresh variable to distribute.
    let argTy' = Scaled mult $ Subst.ty subst argTy
    let (fresh, subst') = subst & Subst.scope %~~ freshId "distributed" argTy'

    -- Distribute the variable and place it as an abstraction outside of the
    -- case expression.
    expr <- distribute' subst' fun $ \subst'' rhs -> do
      -- We transform the fresh variable here, though this should be a no-op!
      fresh' <- continue subst'' $ Var fresh
      pure $ App rhs fresh'
    pure $ Lam fresh expr

  -- Inline function into case
  App fun arg@Case {} -> do
    distribute' subst arg $ \subst' rhs -> do
      fun' <- continue subst' fun
      pure $ App fun' rhs

  -- Inline cast into case
  Cast expr@Case {} co -> do
    distribute' subst expr $ \subst' rhs -> do
      let co' = Subst.co subst' co
      pure $ Cast rhs co'

  _ -> empty
  where
    -- | Different ordering on distribute function for easier use.
    --
    -- It also encloses the continue, since this never changes.
    distribute' subst' expr adjust = do
      distribute adjust continue subst' expr

-- | Distributes a map over a case expression.
--
-- This will ensure correct variable capturing, given that the substitution map
-- includes all variables bound by the result of the mapping function. Note that
-- the mapping function is **not** expected to substitute the right-hand-side;
-- this already happens prior to the map using the given substitution. It should
-- only use the substition map to substitute whatever is being distributed.
distribute
  :: Alternative m
  => Monad m
  => Subst.Class s
  => (s -> CoreExpr -> m CoreExpr)
  -> Transform m s CoreExpr
distribute dist continue subst = \case
  Case scrut bndr _ alts -> do
    -- Continue on the scrutinee.
    scrut' <- continue subst scrut

    -- Distribute over the right-hand-sides using the helper function.
    let (bndr', subst') = subst & Subst.bndr bndr
    alts' <- forM alts $ \(Alt con bndrs rhs) -> do
      -- First deshadow the alternative like normal.
      let (bndrs', subst'') = subst' & Subst.bndrs bndrs
      rhs' <- continue subst'' rhs

      -- We now extend the in-scope set of the original substitution to contain
      -- the binders. This way, any substitions that the distribution function
      -- may do can avoid variable shadowing.
      let scopedSubst = subst & Subst.scope .~ subst'' ^. Subst.scope
      rhs'' <- dist scopedSubst rhs'

      -- Return the new expression with a term distributed over the
      -- right-hand-side.
      pure $ Alt con bndrs' rhs''

    -- Get the type of the new alternatives.
    let ty' = coreAltsType alts'

    -- Return the new case expression, with adjusted alts.
    pure $ Case scrut' bndr' ty' alts'

  _ -> empty

-- TODO: We could do a similar thing with patterns where a default case (for
-- infinite patterns only of course) can be equivalent to an explicit pattern.
-- We could merge the explicit pattern into the default.
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
  Case scrut bndr _ alts -> do
    -- Check if all alts do not bind any of their pattern (which would make
    -- them not equivalent due to different binding variables).
    let unbound (Alt _ bndrs _) = all isDeadBinder bndrs
    guard $ all unbound alts

    -- Check if all alts are equivalent, modulo free variables. Also returns
    -- this equivalent entry if it exists, as we'll use it later. Note we don't
    -- need to check the variables introduced by the alt as we already checked
    -- that they are unbound!
    let cmp (Alt _ _ rhs) (Alt _ _ rhs') = eqCoreExpr rhs rhs'
    expr <- case nubBy cmp alts of
      [Alt _ _ rhs] -> pure rhs
      _ -> empty

    -- We substitute the case binder in the new expression for the new
    -- scrutinee.
    scrut' <- continue subst scrut
    let subst' = subst & Subst.extend bndr scrut'
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
    -- FIXME: Some case binders may never be dead (think of default cases). For
    -- numeric altcons for example, we cannot get rid of default branches. How
    -- do we decide not to run for those? Ideally, we just always run this pass
    -- btw. The problem is that that behaviour gets in the way of other passes
    -- in the current framework.
    guard . not $ isDeadBinder bndr

    -- Substitute the scrutinee and type like normal.
    scrut' <- continue subst scrut
    let ty' = Subst.ty subst ty

    -- Substitute the case binder like normal
    let (bndr', subst') = subst & Subst.bndr bndr

    -- For every alt, substitute the case binder by the alt constructor if
    -- possible.
    alts' <- forM alts $ \(Alt con bndrs rhs) -> do
      -- Substitute the binders, zapping the occurrence info.
      let (bndrs', subst'') = subst' & Subst.bndrs (zapIdOccInfo <$> bndrs)

      -- The expression to substitute the case binder with in this alternative.
      expr <- case con of
        DEFAULT -> do
          -- Fetch all alternatives that this expression is not.
          let others = filter (/= DEFAULT) $ alts <&> \(Alt con' _ _) -> con'

          -- Propagate this information by binding this to the unfolding.
          let bndr'' = setIdUnfolding bndr' $ OtherCon others
          pure $ Var bndr''

        _ -> do
          -- Create an expression from the alt.
          let scope = subst'' ^. Subst.scope
          expr <- altConToExpr scope con bndrs'

          -- Ensure the type matches that of the case binder.
          matchExpr scope expr $ varType bndr'

      -- Substitute the rhs.
      let subst''' = subst'' & Subst.extend bndr expr
      rhs' <- continue subst''' rhs
      pure $ Alt con bndrs' rhs'

    -- Return the modified case expression.
    pure $ Case scrut' bndr' ty' alts'

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
dataConToExpr scope dataCon bndrs = do
  -- Create an expression of the data con with blank type variables.
  let spine = Var $ dataConWorkId dataCon
  let tyVars = Type . mkTyVarTy <$> dataConUnivTyVars dataCon
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

    -- Get the constructors for this scrutinee. Note that we only remove default
    -- cases for data constructors. That is, we cannot really do this in the
    -- same way for types with infinite constructors such as literals.
    cons <- maybeM $ do
      (tyCon, _) <- tcSplitTyConApp_maybe $ varType bndr
      dataCons <- tyConDataCons_maybe tyCon
      pure $ dataCons <&> DataAlt

    -- Fetches the alt corresponding to the given constructor, if it exists.
    let originalAlt con = do
          let cmp (Alt con' _ _) = con == con'
          maybeM $ find cmp explicit

    -- Create an explicit alt using the default rhs.
    let explicitDefault con = do
          -- Get binders with types matching the scrutinee/case binder, this
          -- should never fail if you provide a matching bndr dataCon pair.
          let scope = subst ^. Subst.scope
          (bndrs, _) <- freshAltBndrs scope bndr con

          -- Create the default binder with explicit constructor and binders.
          let bndrs' = bndrs <&> (`setIdOccInfo` IAmDead)
          pure $ Alt con bndrs' rhsDefault

    -- Create the new alternatives. Note that they should be ordered in the same
    -- way as the its list of data constructors. For this reason, we first try
    -- to get the original alternative, before constructing the explicit default
    -- case. In the end, all alts are now explicit.
    alts' <- forM cons $ originalAlt <|-|> explicitDefault

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
  -> AltCon
  -> m ([CoreBndr], InScopeSet)
freshAltBndrs scope bndr = \case
  DataAlt dataCon -> do
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

  LitAlt lit -> do
    guard $ varType bndr `eqType` literalType lit
    pure ([], scope)

  DEFAULT -> pure ([], scope)

-- | Merges nested cases.
--
-- When a case has a DEFAULT pattern, any nested cases over the same scrutinee
-- cannot be deduplicated. As such, we instead merge the two cases. This
-- pass only merges adjacent cases (no deep nesting) and thus relies on case
-- reodering to make the cases adjacent.
--
-- FIXME: So there is an issue where sometimes mergeable cases are not adjacent.
-- Not just that, but they never will: a case lives in between the two mergable
-- ones and is ordered there correctly. We would want to merge these cases.
--
-- There's three solutions to this.
-- 1. We merge cases outside of the transform pass.
--    This is kind of ugly though, but could work. I doubt its fast though...
-- 2. We track wild binders separately and always move wild scrutinees inwards.
--    towards their definining case.
--    It's elegant except that every pass now needs to call a separate function
--    for case binders. I guess that in this way, we could actually do scrutCSE
--    as well, since we also need to know the scrutinees for binders in that
--    example.
-- 3. We have two separate passes, both in different directions. The first is
--    inner to outer. This will tell any case (with default) which branches are
--    explicitely handled by some inner case expression. We can simply duplicate
--    the current default branch as explicit alt with dead binders for each
--    of these. Of course, we still keep the normal default btw. With this, the
--    case-binder-reduce pass will "merge"/deduplicate these inner branches.
--
--    This does however not work for the remaining default branch and any nested
--    cases there. Luckily, we do know that in these cases, only the default
--    alternative is actually ever chosen. An outer to inner pass can solve
--    this, with the knowledge that a particular case binder **cannot** be a set
--    of alternative, such that only the default pattern remains. Keep in mind
--    that this needs to be a substitution, since we need to substitute the
--    case binder for scrutinee.
--
-- So far, the last one seems by far the best to me. It's just that it doesn't
-- quite fit in the current framework. The inner-to-outer direction could
-- be sort of shoe-horned on top, as it could just be called on whatever is
-- returned from the transformation. Not pretty, but workable.
--
-- The other one is a bit more problematic: We now need an additional thing
-- to track which alternatives a case binder cannot inhibit. Wait, there is
-- actually an unfolding for this now that I think about. We could just track it
-- through there I think. Still though, now every transformation would need to
-- add this information for the pass to work efficiently (technically just
-- doing it for deShadowExpr would be correct, but not efficient).
--
-- I feel like I want a more structured way to pass through this type of
-- information. It would be tremendously helpful for scrutCSE. Actually,
-- it would also be really nice for caseSwap, as now we kind of shoe-horned
-- variable ordering tracking for this one as well...
--
-- My current view on this is that we require some helper function for building
-- expressions. These take for every argument a substitution and expression and
-- build up this context.
--
-- The idea is that any pass creates a (possible empty) expression part tells it
-- how to compose with the remaining parts on which we continue. For example, if
-- we were to build a lambda expression like the following:
-- let (x', subst') = subst & Subst.bndr x'
-- e' <- continue subst' e
-- Lam x' e'
--
-- We actually have "set in stone" that the expression will at least define
-- binder x' through the lambda. We don't know yet what e' will look like.
-- Ideally we can use the knowledge that the expression for sure looks like
-- Lam x' ?
-- when we actually call continue on e.
--
-- That's why I'm thinking. Wouldn't it make sense to have some set of functions
-- that can be used as follows:
--
-- let (x', subst') = subst & Subst.bndr x'
-- mkLam continue x' (subst', e)
--
-- Or something along these lines. This could allow any auxiliary function to
-- track whatever it is that is required before calling continue. Think of
-- variable declaration order, scrutinee binder pairs for scrutCSE, OtherCon
-- unfoldings for removing defaults.
--
-- Another thing though: I don't want to shoe-horn inner-to-outer passes. We
-- currently only have outer-to-inner passes. That is, passes where we pass
-- along some data to the inner components (variable ordering, substitutions,
-- etc.). For the part of the case merging where we want to 
-- TODO: Remove this stuff. We maybe want to retain the comment explaining
-- case merging in the new framework!
-- caseMerge
--   :: Alternative m
--   => Monad m
--   => Subst.Class s
--   => Transform m s CoreExpr
-- caseMerge continue subst = \case
--   Case oScrut oBndr oTy (Alt DEFAULT _ (Case iScrut iBndr _ iAlts) : oAlts) -> do
--     -- Ensure that the cases scrutinize the same expression.
--     guard $ eqCoreExpr (Var oBndr) iScrut || eqCoreExpr oScrut iScrut

--     oScrut' <- continue subst oScrut
--     let oTy' = Subst.ty subst oTy
--     -- Continue on the outer alts.
--     let (oBndr', subst') = subst & Subst.bndr oBndr
--     oAlts' <- deShadowAlts continue subst' oAlts

--     -- TODO: This is a bit redundant. We're actually computing continue for
--     -- expressions we will later discard...
--     -- Continue on the inner alts, substituting the case binder.
--     let subst'' = subst' & Subst.extend iBndr (Var oBndr')
--     iAlts' <- deShadowAlts continue subst'' iAlts

--     -- Merge the alternatives. Note that we provide the outer alts first as they
--     -- should be prioritised. We purposely leave out the default case in this
--     -- merge. Otherwise, it would be a no-op.
--     let oAlts'' = mergeAlts oAlts' iAlts'
--     pure $ Case oScrut' oBndr' oTy' oAlts''

--   _ -> empty

-- | Swap nested case expressions according.
--
-- Swap nested cases based on their scrutinees. We order based on the
-- declaration order of variables in the scrutinees. Of course, this will not
-- swap for any scrutinee that depends on the binders of its encapsulating
-- scrutinee.
caseSwap
  :: Alternative m
  => Monad m
  => Transform m Subst.Ordered CoreExpr
caseSwap continue subst = \case
  Case oScrut oBndr oTy oAlts -> do
    -- Get the unbound alt as an irrefutable pattern.
    (oConSwap, oBndrsSwap, (iScrut, iBndr, iTy, iAlts)) <- asum $ oAlts <&> \case
      Alt con bndrs (Case iScrut iBndr iTy iAlts) -> do
        -- Checks whether the cases are swappable.
        guard $ exprFreeVars iScrut `disjointVarSet` mkVarSet (oBndr : bndrs)

        -- Checks whether we should reorder the cases, according to some
        -- ordering based on the scrutinees.
        guard $ LT == compareScrut subst oScrut iScrut

        -- We want to minimize swapping, as it is a very expensive operation.
        -- The comparison function only actually makes sense for primitive
        -- scrutinees. Otherwise, we might redundantly swap back and forth.
        guard $ all (isPrimitive subst) [oScrut, iScrut]

        -- Irrefutable pattern of the inner case.
        pure (con, bndrs, (iScrut, iBndr, iTy, iAlts))
      _ -> empty

    -- Create a substitution map given that we take this swap alternative.
    let (oBndr', iSubst) = subst & Subst.bndr oBndr
    let (oBndrsSwap', iSubst') = iSubst & Subst.bndrs oBndrsSwap

    -- Calculate the new inner case in its entirety, given the outer swap
    -- alternative binder substitution is in scope.
    iScrut' <- continue iSubst' iScrut
    let iTy' = Subst.ty iSubst' iTy
    let (iBndr', iSubst'') = iSubst' & Subst.bndr iBndr

    -- Note how the alts are still incomplete here. For the final swap, we
    -- expect the outer case to occur for every right-hand-side.
    iAlts' <- deShadowAlts continue iSubst'' iAlts

    -- Gather an overapproximate in-scope set. This will additionally carry the
    -- uniques that are used by the new binders of the inner case expression.
    -- I.e. both the case binder and alternative binders. We need this solely
    -- to avoid shadowing.
    let accumulate scope (Alt _ bndrs _) = extendInScopeSetList scope bndrs
    let used = foldl' accumulate emptyInScopeSet iAlts'
    let used' = extendInScopeSet used iBndr'
    let scope = unionInScope used' $ iSubst ^. Subst.scope

    -- Use this overapproximate in-scope set to calculate the new outer case.
    -- The exception being the swap alternative. We just skip it at first, it
    -- will be replaced in the next step!
    let oSubst = subst & Subst.scope .~ scope
    oScrut' <- continue oSubst oScrut
    let oTy' = Subst.ty oSubst oTy

    -- Note how we carefully take the substitution map containing the outer case
    -- binder substitution here.
    let oSubst' = iSubst & Subst.scope .~ scope
    oAlts' <- forM oAlts $ \alt -> case alt of
      Alt con _ _ | con == oConSwap -> pure $ Alt con oBndrsSwap' undefined
      _ -> deShadowAlt continue oSubst' alt

    -- This function takes a right-hand-side expression and places it inside
    -- of the swap alternative. The intention is that we will populate the
    -- right-hand-side with the branches of the inner case.
    let replace rhs = Case oScrut' oBndr' oTy' $ oAlts' <&> \case
          Alt con bndrs _ | con == oConSwap -> Alt con bndrs rhs
          alt -> alt

    -- Populate the right-hand-side of every inner alternative with the full
    -- outer case.
    let iAlts'' = iAlts' <&> \(Alt con bndrs rhs) -> do
          Alt con bndrs $ replace rhs

    -- Return the new, swapped case.
    pure $ Case iScrut' iBndr' iTy' iAlts''

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
  -- Variable in first position.
  (Var x, Var y) -> Subst.compareVar subst x y
  (Var _, Lit _) -> GT
  (Var _, App _ _) -> GT
  (Var _, Cast _ _) -> GT

  -- Literal in first position.
  (Lit _, Var _) -> LT
  (Lit x, Lit y) -> compare x y
  (Lit _, App _ _) -> GT
  (Lit _, Cast _ _) -> GT

  -- Application in first posistion.
  (App _ _, Var _) -> LT
  (App _ _, Lit _) -> LT
  (App f a, App f' a') -> compareScrut subst f f' <> compareScrut subst a a'
  (App _ _, Cast _ _) -> GT

  -- Cast in first posistion.
  (Cast _ _, Var _) -> LT
  (Cast _ _, Lit _) -> LT
  (Cast _ _, App _ _) -> LT
  (Cast e _, Cast e' _) -> compareScrut subst e e'

  -- We don't want to reorder other types of scrutinees.
  _ -> EQ

isPrimitive :: Subst.Class s => s -> CoreExpr -> Bool
isPrimitive subst = \case
  Var v -> isNothing $ Subst.lookupId' subst v
  Lit _ -> True
  Coercion _ -> True
  Type _ -> True
  Cast expr _ -> isPrimitive subst expr
  App fun arg -> all (isPrimitive subst) [fun, arg]
  _ -> False

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

scrutCSE' :: CoreExpr -> CoreExpr
scrutCSE' = scrutCSE emptyTM

-- | Perform Common Sub-Expression Elminiation on scrutinees.
--
-- Note that this expect the expression to not have any variable shadowing.
-- TODO: Ideally this is somehow part of the pass infrastructure!
scrutCSE :: CoreMap Var -> CoreExpr -> CoreExpr
scrutCSE common = \case
  Case scrut bndr ty alts -> do
    let scrut' = maybe scrut Var $ lookupTM scrut common
    let bndr' = zapIdOccInfo bndr

    let common' = insertTM scrut bndr' common
    let alts' = alts <&> \(Alt con bndrs rhs) -> do
          let rhs' = scrutCSE common' rhs
          Alt con bndrs rhs'

    Case scrut' bndr' ty alts'

  expr -> gmapT (mkT $ scrutCSE common) expr

prepCaseDedup' :: InScopeSet -> CoreExpr -> CoreExpr
prepCaseDedup' = fst .: prepCaseDedup

prepCaseDedup :: InScopeSet -> CoreExpr -> (CoreExpr, Map Var (Set AltCon))
prepCaseDedup scope = \case
  Case scrut bndr ty alts | (explicit, rhsDefault) <- findDefault alts -> do
    let scope' = extendInScopeSet scope bndr

    -- Recurse for all explicit alternatives.
    let (explicit', altMaps) = unzip $ explicit <&> \(Alt con bndrs rhs) -> do
          let scope'' = extendInScopeSetList scope' bndrs
          let (rhs', altMap) = prepCaseDedup scope'' rhs
          (Alt con bndrs rhs', altMap)

    let (additional, addAltMap) = fromMaybe (mempty, mempty) $ do
          -- Recurse for the default alternative.
          rhs <- rhsDefault
          let (rhs', altMap) = prepCaseDedup scope' rhs

          -- Fetch the alternative constructors we are missing.
          let nested = fromMaybe mempty $ lookupTM bndr altMap
          let used = explicit' <&> \(Alt con _ _) -> con
          let missing = Set.toList $ foldl' (flip Set.delete) nested used

          -- Create the missing alternatives.
          let missing' = missing <&> \con -> do
                -- TODO: We are shadowing variables here. Ideally, we just don't as
                -- many passes expect fully non-shadowed expressions. I think the only
                -- to not have this shadow would be to run a full substitution.
                let (bndrs, _) = fromJust $ freshAltBndrs scope bndr con
                Alt con bndrs rhs'

          -- Since we cannot eliminate the default alt, we also add it here.
          -- FIXME: In some cases, this will actually remove all defaults. I
          -- guess our other pass deals with those cases, but still this is not
          -- nice.
          let defaultAlt = Alt DEFAULT [] rhs'

          pure (defaultAlt : missing', altMap)

    -- Merge the missing alternatives into the original alternatives.
    let cmp (Alt con _ _) (Alt con' _ _) = compare con con'
    let alts' = sortBy cmp $ additional <> explicit'

    -- New case statement, with the alternatives included.
    let expr = Case scrut bndr ty alts'

    -- Gather all used explicit patterns for every scrutinee.
    let altMap' = Map.unionsWith (<>) $ addAltMap : altMaps
    let altMap'' = case scrut of
          Var scrut' -> do
            let insert s (Alt DEFAULT _ _) = s
                insert s (Alt con _ _) = Set.insert con s
            let current = foldl' insert mempty alts'
            Map.insert scrut' current altMap'
          _ -> altMap'

    (expr, altMap'')

  App fun arg -> do
    let (fun', fAltMap) = prepCaseDedup scope fun
    let (arg', aAltMap) = prepCaseDedup scope arg
    let expr = App fun' arg'
    let altMap = Map.unionWith (<>) fAltMap aAltMap
    (expr, altMap)

  Tick tickish expr -> do
    let (expr', altMap) = prepCaseDedup scope expr
    (Tick tickish expr', altMap)

  Cast expr co -> do
    let (expr', altMap) = prepCaseDedup scope expr
    (Cast expr' co, altMap)

  Lam bndr body -> do
    let scope' = extendInScopeSet scope bndr
    let (body', altMap) = prepCaseDedup scope' body
    let expr = Lam bndr body'
    (expr, altMap)

  -- TODO: We can just skip it for now, since we don't really have let bindings
  -- but I guess this isn't very nice.
  Let bind body -> (Let bind body, mempty)

  e -> (e, mempty)
