{-# LANGUAGE ScopedTypeVariables #-}

module UC
  ( plugin
  , UC (..)
  , UCCompare (..)
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Lint
import GHC.Driver.Config.Core.Lint (initLintConfig)
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
import GHC.Core.Map.Expr
import GHC.Tc.Utils.TcType (eqType)

import GHC.MonadCore

import qualified Data.Map as Map
import Data.Map (Map)
import Data.List (foldl', nubBy)
import Data.Maybe (fromMaybe, fromJust, catMaybes)

import Data.Data
import Generics.SYB hiding (empty)

import Control.Applicative (Alternative (..), empty, asum)
import Control.Monad (guard, forM, foldM, unless, (>=>))
import Control.Monad.Trans.Maybe

import qualified Language.Haskell.TH.Syntax as TH

import qualified Projection
import Types
import Util

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

-- TODO: Change printUCGenerated to printAnnotated, which should take a type
-- parameter.
install :: MonadCore m => [CommandLineOption] -> Pass m [CoreToDo]
install _ todo = return $ checkPasses <> cmpPasses <> inferPasses <> todo
  where
    cmpPasses = [CoreDoPluginPass "compareNormalforms" compareNormalforms]

    checkPasses = [doCheck]

    proxy = Proxy @(UCGenerated (UC TH.Name))
    inferPasses =
      [ CoreDoPluginPass "CreateInferenceBinds" createInferenceBinds
      , CoreDoPluginPass "ProjectOutput" projectOutput
      , inlineAllPass proxy
      , dedupCasesPass proxy
      -- , printAndLintPass proxy
      -- , CoreDoPluginPass "SplitExprs" splitExprs
      -- , CoreDoPluginPass "splitExpr" $ splitExprs proxy
      , printAndLintPass proxy
      -- , CoreDoPluginPass "PrintUCGenerated" printUCGenerated
      -- , CoreLiberateCase
      -- , CoreDoPluginPass "PrintUCGenerated" printUCGenerated
      , CoreDoPluginPass "RemoveUCBinds" removeUCBinds
      ]
      -- [ CoreDoPluginPass "CreateUCBinds" createUCBinds
      -- -- , CoreDoPluginPass "PrintUCGenerated" printUCGenerated
      -- , CoreDoPluginPass "InlineAll" inlineAll
      -- , CoreDoPluginPass "DedupCases" dedupCases
      -- -- , CoreDoPluginPass "SplitExprs" splitExprs
      -- -- , CoreDoPluginPass "PrintUCGenerated" printUCGenerated
      -- -- , CoreLiberateCase
      -- , CoreDoPluginPass "PrintUCGenerated" printUCGenerated
      -- , CoreDoPluginPass "RemoveUCBinds" removeUCBinds
      -- ]

createInferenceBinds :: MonadFail m => MonadCore m => Pass m ModGuts
createInferenceBinds = createUCBinds $ return @_ @(UC TH.Name)

createUCBinds
  :: forall m a b. (Data a, Data b, MonadFail m, MonadCore m)
  => (a -> m b)
  -> Pass m ModGuts
createUCBinds f guts = do
  -- FIXME: We should check that there exists strictly one annotation per bind
  -- and that all of them are non-recursive.
  (_, anns) <- liftCore $ getFirstAnnotations @a deserializeWithData guts

  -- Runs the function on the given CoreBind, given that the CoreBind is
  -- non-recursive.
  let genBind :: CoreBind -> m (Maybe (b, CoreBind'))
      genBind = \case
        NonRec var expr -> do
          let ann = lookupUFM anns $ varName var
          let attachBind a = do
                let name = "ucgenerated_" <> occNameString (occName var)
                var' <- freshGlobalVar name $ varType var
                b <- f a
                return (b, Bind' var' expr)
          forM ann attachBind
        _ -> fail "UC annotations cannot occur on recursive definitions"

  -- Get all generated bindings.
  gen <- catMaybes <$> mapM genBind (mg_binds guts)
  let annots = uncurry ucGenAnn <$> gen
  let binds = nonRec . snd <$> gen

  -- Return the guts with the additional binders.
  return guts
    { mg_binds = binds <> mg_binds guts
    , mg_anns = annots <> mg_anns guts
    }

-- | Run the given pass on all binders that have the given annotation.
annBindsPass
  :: forall m a. (Data a, MonadCore m)
  => (a -> Pass m CoreBind')
  -> Pass m ModGuts
annBindsPass pass guts = do
  (_, anns) <- liftCore $ getFirstAnnotations @a deserializeWithData guts

  binds <- forM (mg_binds guts) $ \case
    NonRec x e | Just ann <- lookupUFM anns $ varName x
      -> nonRec <$> pass ann (Bind' x e)
    b -> return b

  return guts { mg_binds = binds }

printAndLintPass
  :: forall a proxy. Data a
  => proxy a
  -> CoreToDo
printAndLintPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'printAndLintPass
    pass = annBindsPass $ \(_ :: a) -> printAndLint

inlineAllPass
  :: forall a proxy. Data a
  => proxy a
  -> CoreToDo
inlineAllPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'inlineAllPass
    pass = annBindsPass $ \(_ :: a) -> inlineAll

dedupCasesPass
  :: forall a proxy. Data a
  => proxy a
  -> CoreToDo
dedupCasesPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'dedupCasesPass
    pass = annBindsPass $ \(_ :: a) -> dedupCases

doCheck :: CoreToDo
doCheck = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'doCheck
    pass guts = annBindsPass (doCheck' $ mg_binds guts) guts

doCheck' :: (MonadCore m, MonadFail m) => CoreProgram -> UCCheck TH.Name -> Pass m CoreBind'
doCheck' prog uc bind = do
  let resolve name = resolveTH prog name
        ??= "Could not resolve function: " <> TH.nameBase name

  -- Fetch projection functions
  sproj <- resolve 'Projection.sproj
  sproj' <- resolve 'Projection.sproj'
  iproj <- resolve 'Projection.iproj
  oproj <- resolve 'Projection.oproj

  obs <- resolve $ ch_obs uc
  impl <- resolve $ ch_impl uc

  leak <- resolve $ ch_leak uc
  sim <- resolve $ ch_sim uc

  ignfun <- resolve $ ch_ignfun uc
  ignsim <- resolve $ ch_ignsim uc

  let show' :: Outputable o => o -> String
      show' = showSDocUnsafe . ppr

  let app (Bind' lvar lexpr) (Bind' rvar rexpr) = do
        let showvar var = "(" <> show' var <> " :: " <> show' (varType var) <> ")"
        expr <- polyApp lexpr rexpr
          ??= "Incompatible application: \n" <> showvar lvar <> "\n" <> showvar rvar
        var <- freshLocalVar "fresh" $ exprType expr
        return $ Bind' var expr

  let app' fun args = do
        Bind' var expr <- foldM app fun args
        return $ Bind' var (occurAnalyseExpr expr)

  let normalize = inlineAll >=> dedupCases

  let cmp errmsg lhs rhs = do
        lhs'@(Bind' lvar lexp) <- normalize lhs
        rhs'@(Bind' rvar rexp) <- normalize rhs
        unless (lexp `eqCoreExpr` rexp) $ do
          dbg lhs'
          dbg rhs'
          fail $ errmsg <> ": " <> show' lvar <> " =/= " <> show' rvar

  oprojected <- app' oproj [obs, impl]
  sprojected <- app' sproj [ignfun, oprojected]
  sprojected' <- app' sproj' [ignfun, ignsim]

  cmp "State projection not equal" sprojected sprojected'

  iprojected <- app' iproj [leak, sim]

  cmp "Input projection not equal" sprojected' iprojected

  return bind

-- projectOutputPass :: CoreToDo
-- projectOutputPass = CoreDoPluginPass name pass
--   where
--     name = TH.nameBase 'projectOutputPass
--     pass = ucBindsPass projectOutput

printAndLint :: MonadCore m => Pass m CoreBind'
printAndLint bind = do
  dflags <- liftCore getDynFlags
  let cfg = initLintConfig dflags []
  let res = lintCoreBindings' cfg [nonRec bind]
  dbg bind
  dbg res
  return bind

inlineAll :: MonadCore m => Pass m CoreBind'
inlineAll (Bind' x e) = do
  let fused = fuse
        [ betaReduce
        , inlineUnfolding
        , caseDistribute
        , foldCase
        , redundantCase
        , extractLambda
        , undefaultCase
        ]

  e' <- occurAnalyseExpr <$> fix fused e
  return $ Bind' x e'

-- TODO: Rename this!
dedupCases :: MonadCore m => Pass m CoreBind'
dedupCases (Bind' x e) = do
  e' <- occurAnalyseExpr <$> dedupCase Map.empty e
  return $ Bind' x e'

-- | Project the output of all generated UC binders, according to the
-- observation function in the annotation.
projectOutput :: MonadFail m => MonadCore m => Pass m ModGuts
projectOutput guts = flip annBindsPass guts $ \(UCGenerated uc) (Bind' var expr) -> do
  let prog = mg_binds guts

  Bind' _ oproj <- resolveTH prog 'Projection.oproj
    ??= "Could not fetch output projection function"

  Bind' _ obs <- resolveTH prog (observable uc)
    ??= "Could not fetch the observation function."

  expr' <- occurAnalyseExpr <$> foldM polyApp oproj [obs, expr]
    ??= "Incompatible types on observation/implementation pair"

  let var' = setVarType var $ exprType expr'
  return $ Bind' var' expr'

compareNormalforms :: MonadFail m => MonadCore m => Pass m ModGuts
compareNormalforms guts = flip annBindsPass guts $ \(UCCompare other) bind -> do
  let prog = mg_binds guts

  let normalize :: MonadCore m => Pass m CoreBind'
      normalize = inlineAll >=> dedupCases

  other' <- resolveTH prog other
    ??= "Could not fetch output projection function"

  lhs <- normalize other'
  rhs <- normalize bind
  let cmp (Bind' _ l) (Bind' _ r) = eqCoreExpr l r
  unless (lhs `cmp` rhs) $ do
    dbg other'
    dbg lhs
    dbg bind
    dbg rhs
    fail "Expressions were non-equal"
  return bind

splitExprs
  :: forall a m proxy. Data a
  => MonadCore m
  => proxy a
  -> Pass m ModGuts
splitExprs _ = annBindsPass $ \(_ :: a) (Bind' x e) -> do
  let fused = fuse
        [ redundantCase
        , caseFactor
        ]

  e' <- occurAnalyseExpr <$> fix fused e
  return $ Bind' x e'


-- TODO: Implement this!
removeUCBinds :: MonadCore m => Pass m ModGuts
removeUCBinds guts = do
  return guts

-- | Run the given pass until a fixed point is reached. That is, the given pass
-- does not produce a new result.
fix :: (MonadCore m, Data a) => Pass (MaybeT m) a -> Pass m a
fix f = everywhereM $ mkM go
  where
    go e = runMaybeT (f e) >>= \case
      Just e' -> fix f e'
      Nothing -> return e

-- | Fuse all the given passes; the first succesful pass wil return its result.
fuse :: Alternative m => [Pass m CoreExpr] -> Pass m CoreExpr
fuse = foldl' fuse' $ const empty

-- | Fuses two passes; the first succesful pass will return its result.
fuse' :: Alternative m => Pass m CoreExpr -> Pass m CoreExpr -> Pass m CoreExpr
fuse' p p' e = p e <|> p' e

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

-- | Inlines all non-typeclass functions.
inlineUnfolding :: (Alternative m, Monad m) => Pass m CoreExpr
inlineUnfolding = \case
  Var x
    | not $ isClassOpId x
    , CoreUnfolding { uf_tmpl = expr } <- idUnfolding x -> return expr
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

-- | Distrubte expressions over a case. This pushes case expressions towards the
-- root of the expression.
caseDistribute :: (Alternative m, MonadCore m) => Pass m CoreExpr
caseDistribute = \case
  -- Nested case
  Case cas@Case {} bind ty alts -> do
    temp <- tempVar $ exprType cas
    let fun = Lam temp (Case (Var temp) bind ty alts)
    distribute fun cas

  -- Inline argument into case
  App cas@Case {} arg -> do
    temp <- tempVar $ exprType cas
    let fun = Lam temp (App (Var temp) arg)
    distribute fun cas

  -- Inline function into case
  App fun cas@Case {} -> distribute fun cas

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

-- reorderCases :: (Alternative m, MonadCore m) => Pass m CoreExpr
-- reorderCases = \case
--   Case scrut bind ty alts -> do
--     empty

--   _ -> empty

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

-- FIXME: I think there is an issue with the fold given a default branch:
-- we cannot always fold a branch in this case I think. Maybe we could do
-- something like include it in the outer case?
--
-- FIXME: The below statement doesn't always seem to be true.
-- Occurence check already makes sure that we use the binder in a case instead
-- of another copy of the scrutinized expression. As such, the key in the Map
-- can actually be a variable instead of an expression.
dedupCase :: Monad m => Map CoreBndr (AltCon, [CoreBndr]) -> Pass m CoreExpr
dedupCase scruts = \case
  -- We have case split over this scrutinee if we enter this case. Thus, we can
  -- remove the case split by selecting the branch that was taken previously.
  -- We take care of the binders in the term to reference the outer case.
  Case (Var scrut) bind _ alts | Just (c, bs) <- Map.lookup scrut scruts -> do
    -- A matching alt should always be available.
    let Alt _ bs' rhs = fromJust $ findAlt c alts

    -- Map all the binders of the case to the expressions along the spine.
    -- Additionally, the binder should be substituted by the scrutinee.
    let mapping = (bind, Var scrut) : zip bs' (Var <$> bs)

    -- Get the inscope variables.
    let inscope = mkInScopeSet $ exprFreeVars rhs

    -- Make the substition using the mapping and perform the substitution.
    let subst = extendSubstList (mkEmptySubst inscope) mapping

    -- Substitute the alts in the expression.
    let expr = substExpr subst rhs

    -- Attempt to fold more cases in the new expression.
    dedupCase scruts expr

  -- We have not case split over this scrutinee before, thus we add it to the
  -- map and continue. We do not have to traverse the scrutinee itself for the
  -- fold in this scenario, as the case distribute pass makes sure that no
  -- scrutinee can contain a case.
  Case scrut bind ty alts -> do
    let withAlt (Alt c bs rhs) = do
          -- We remove the occurence info (may occur many times), as it may do
          -- so after deduplicating a case. The occurence analysis doesn't catch
          -- this, so we do it manually.
          let bs' = flip setIdOccInfo noOccInfo <$> bs
          let scruts' = Map.insert bind (c, bs') scruts
          rhs' <- dedupCase scruts' rhs
          return $ Alt c bs rhs'

    Case scrut bind ty <$> mapM withAlt alts

  e -> gmapM (mkM $ dedupCase scruts) e
