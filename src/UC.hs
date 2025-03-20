module UC
  ( plugin
  , UC (..)
  , UCCompare (..)
  , UCNorm (..)
  , SymCompare (..)
  , Spec (..)
  , Projection.Circuit
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Lint
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
import GHC.Core.Map.Expr (eqCoreExpr)
import GHC.Driver.Config.Core.Lint (initLintConfig)
import GHC.MonadCore

import Data.Maybe (catMaybes)
import Data.Data

import Control.Monad.Reader (MonadReader, ReaderT (..), reader)
import Control.Monad (forM, unless)

import qualified Language.Haskell.TH.Syntax as TH

import qualified Lint
import qualified Projection
-- Import the RULES defined in Diverge.
import Diverge ()
import Types
import Util
import Transform
import Unification
import Symbolic.Solve
import Monomorph (monomorphize)

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

-- TODO: We should take in a flag which tells normalisation to lint intermediate
-- steps! Maybe we can just call it debug?
install :: MonadCore m => [CommandLineOption] -> Pass m [CoreToDo]
install _ todo = pure $ mconcat
  [ symComparePasses
  , checkSpecPasses
  , normalizePasses
  , comparePasses
  , tacticPasses
  , todo
  ]
  where
    withProxy proxy ls = ($ proxy) <$> ls

    symComparePasses = withProxy (Proxy @(UCGenerated (SymCompare TH.Name)))
      [ createUCBindsPass
      , printAndLintPass
      , symComparePass
      , removeUCBindsPass
      ]

    -- TODO: I don't really need to create new binds to do this pass, since I'm
    -- not modifying the binds anyway.
    checkSpecPasses = withProxy (Proxy @(UCGenerated (Spec TH.Name)))
      [ createUCBindsPass
      , printAndLintPass
      , checkSpecPass
      , removeUCBindsPass
      ]

    normalizePasses = withProxy (Proxy @(UCGenerated UCNorm))
      [ createUCBindsPass
      , printAndLintPass
      , normalizePass
      , printAndLintPass
      , removeUCBindsPass
      ]

    comparePasses = withProxy (Proxy @(UCGenerated (UCCompare TH.Name)))
      [ createUCBindsPass
      , ucComparePass
      , printAndLintPass
      , removeUCBindsPass
      ]

    tacticPasses = withProxy (Proxy @(UCGenerated (UC TH.Name)))
      [ createUCBindsPass
      , ucCheckPass
      , printAndLintPass
      , removeUCBindsPass
      ]

createUCBinds
  :: forall m a b
   . Data a
  => Data b
  => MonadFail m
  => MonadCore m
  => (a -> m b)
  -> Pass m ModGuts
createUCBinds f guts = do
  -- FIXME: We should check that there exists strictly one annotation per bind
  -- (and ideally that all of them are non-recursive).
  (_, anns) <- liftCore $ getFirstAnnotations @a deserializeWithData guts

  -- Runs the function on the given CoreBind, given that the CoreBind is
  -- non-recursive.
  let genBind :: CoreBind -> m (Maybe (b, CoreBind'))
      genBind = \case
        NonRec var expr | Just ann <- lookupUFM anns $ varName var -> do
          let name = "ucgenerated_" <> occNameString (occName var)
          var' <- freshGlobalVar name $ varType var
          ann' <- f ann
          let bind = Bind' var' expr
          return $ Just (ann', bind)
        _ -> return Nothing

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
  :: forall m a
   . Data a
  => MonadCore m
  => (a -> Pass m CoreBind')
  -> Pass m ModGuts
annBindsPass pass guts = do
  (_, anns) <- liftCore $ getFirstAnnotations @a deserializeWithData guts

  binds <- forM (mg_binds guts) $ \case
    NonRec x e | Just ann <- lookupUFM anns $ varName x -> do
      nonRec <$> pass ann (Bind' x e)
    b -> return b

  return guts { mg_binds = binds }

annBindsPassWithGuts
  :: MonadCore m
  => Data a
  => (a -> Pass (ReaderT ModGuts m) CoreBind')
  -> Pass m ModGuts
annBindsPassWithGuts f mods = annBindsPass f' mods
  where
    f' a = flip runReaderT mods . f a

createUCBindsPass
  :: forall a
   . Data a
  => Proxy (UCGenerated a)
  -> CoreToDo
createUCBindsPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'createUCBindsPass
    pass = createUCBinds $ return @_ @a

removeUCBindsPass :: Proxy (UCGenerated a) -> CoreToDo
removeUCBindsPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'removeUCBindsPass
    pass = removeUCBinds

printAndLintPass
  :: forall a
   . Data a
  => Proxy a
  -> CoreToDo
printAndLintPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'printAndLintPass
    pass = annBindsPassWithGuts $ \(_ :: a) -> printAndLint

symComparePass
  :: proxy
  -> CoreToDo
symComparePass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'symComparePass
    pass = annBindsPassWithGuts symCompare

checkSpecPass :: proxy -> CoreToDo
checkSpecPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'checkSpecPass
    pass = annBindsPassWithGuts checkSpec

normalizePass
  :: forall a
   . Data a
  => Proxy a
  -> CoreToDo
normalizePass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'normalizePass
    pass = annBindsPassWithGuts $ \(_ :: a) bind -> do
      guts <- reader modGuts
      bindPass (normalize guts) bind

ucCheckPass :: proxy -> CoreToDo
ucCheckPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'ucCheckPass
    pass = annBindsPassWithGuts ucCheck

ucComparePass :: proxy -> CoreToDo
ucComparePass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'ucComparePass
    pass = annBindsPassWithGuts ucCompare

printAndLint
  :: MonadCore m
  => MonadReader r m
  => HasModGuts r
  => Pass m CoreBind'
printAndLint bind = do
  dflags <- liftCore getDynFlags
  let cfg = initLintConfig dflags []
  prog <- reader $ mg_binds . modGuts
  let res = lintCoreBindings' cfg prog
  dbg bind
  dbg res
  pure bind

-- TODO: Clean up this function. It's pretty much the same as composeSim.
-- It feels as though we could do better...
composeImpl
  :: MonadFail m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
  => UC TH.Name
  -> Pass m CoreExpr
composeImpl uc expr = do
  let resolve name = Var <$> resolveTH' name

  oproj <- resolve 'Projection.oproj
  obs <- resolve $ observation uc

  expr' <- unifyApps oproj [obs, expr]
    ??= "Incompatible types on observation/implementation pair"

  sproj <- resolve 'Projection.sproj
  proj <- resolve $ projection uc

  expr'' <- unifyApps sproj [proj, expr']
    ??= "Incompatible types on (implementation/observation)/projection pair"

  pure $ occurAnalyseExpr expr''

composeImpl'
  :: MonadFail m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
  => Spec TH.Name
  -> Pass m CoreExpr
composeImpl' spec expr = do
  let resolve name = Var <$> resolveTH' name

  compose <- resolve 'Projection.compose
  obs <- resolve $ observation' spec

  expr' <- unifyApps compose [expr, obs]
    ??= "Incompatible types on observation/implementation pair"

  sproj <- resolve 'Projection.sproj
  proj <- resolve $ projection' spec

  expr'' <- unifyApps sproj [proj, expr']
    ??= "Incompatible types on (implementation/observation)/projection pair"

  pure $ occurAnalyseExpr expr''

composeSim'
  :: MonadFail m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
  => Spec TH.Name
  -> m CoreExpr
composeSim' uc = do
  let resolve name = Var <$> resolveTH' name

  compose <- resolve 'Projection.compose
  sproj' <- resolve 'Projection.sproj'

  sim <- resolve $ simulator' uc
  leak <- resolve $ leakage' uc
  proj <- resolve $ projection' uc

  expr' <- unifyApps compose [leak, sim]
    ??= "Incompatible types on leakage/simulator pair"

  expr'' <- unifyApps sproj' [proj, expr']
    ??= "Incompatible types on projection/(leakage/simulator) pair"

  pure $ occurAnalyseExpr expr''

composeSim
  :: MonadFail m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
  => UC TH.Name
  -> m CoreExpr
composeSim uc = do
  let resolve name = Var <$> resolveTH' name

  sim <- resolve $ simulator uc

  iproj <- resolve 'Projection.iproj
  leak <- resolve $ leakage uc

  sproj' <- resolve 'Projection.sproj'
  proj <- resolve $ projection uc

  expr' <- unifyApps iproj [leak, sim]
    ??= "Incompatible types on leakage/simulator pair"

  expr'' <- unifyApps sproj' [proj, expr']
    ??= "Incompatible types on projection/(leakage/simulator) pair"

  pure $ occurAnalyseExpr expr''

ucCheck
  :: MonadFail m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
  => HasDynFlags m
  => UCGenerated (UC TH.Name)
  -> Pass m CoreBind'
ucCheck (UCGenerated uc) (Bind' var expr) = do
  expr' <- composeImpl uc expr
  sim <- composeSim uc

  (sim', expr'') <- unifyAndNorm sim expr'

  -- Check whether they are equal
  unless (expr'' `eqCoreExpr` sim') $ do
    dbg' "implementation:"
    dbg expr''
    dbg' "simulator:"
    dbg sim'
    fail "Implementation does not equal simulator"

  let var' = setVarType var $ exprType expr''
  pure $ Bind' var' expr''

checkSpec
  :: MonadFail m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
  => HasDynFlags m
  => UCGenerated (Spec TH.Name)
  -> Pass m CoreBind'
checkSpec (UCGenerated spec) (Bind' var expr) = do
  guts <- reader modGuts
  let program = mg_binds guts
  let scope = extendInScopeSetBndrs emptyInScopeSet program

  imp <- composeImpl' spec expr
  Lint.panic Lint.base scope imp

  sim <- composeSim' spec
  Lint.panic Lint.base scope sim

  (imp', sim') <- unifyExprs imp sim
    ??= "Unable to unify implementation projection with simulator"

  instEnvs <- getInstEnvs'
  let imp'' = resolveInstances instEnvs imp'
  let sim'' = resolveInstances instEnvs sim'

  imp''' <- monomorphize guts imp''
  Lint.panic Lint.base scope imp'''

  sim''' <- monomorphize guts sim''
  Lint.panic Lint.base scope sim'''

  result <- exprSymEq imp''' sim'''

  case result of
    Right _ -> do
      dbg' "Expressions are equal!"
    Left err -> do
      dbg err
      fail "Expressions are **NOT** equal"

  pure $ Bind' var expr

symCompare
  :: MonadFail m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
  => HasDynFlags m
  => UCGenerated (SymCompare TH.Name)
  -> Pass m CoreBind'
symCompare (UCGenerated (SymCompare other)) (Bind' var expr) = do
  let resolve name = Var <$> resolveTH' name

  guts <- reader modGuts
  expr' <- monomorphize guts expr

  other' <- do
    other' <- resolve other
    monomorphize guts other'

  result <- exprSymEq expr' other'

  case result of
    Right _ -> do
      dbg' "Expressions were equal!"
      pure $ Bind' var expr
    Left err -> do
      dbg err
      fail "Expressions were not equal"

ucCompare
  :: MonadFail m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
  => HasDynFlags m
  => UCGenerated (UCCompare TH.Name)
  -> Pass m CoreBind'
ucCompare (UCGenerated (UCCompare other)) (Bind' var expr) = do
  let resolve name = Var <$> resolveTH' name
  other' <- resolve other

  (expr', other'') <- unifyAndNorm expr other'

  -- Check whether they are equal
  unless (expr' `eqCoreExpr` other'') $ do
    dbg expr'
    dbg other''
    fail "Expressions were not equal"

  pure $ Bind' var expr

unifyAndNorm
  :: MonadFail m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
  => HasDynFlags m
  => CoreExpr
  -> CoreExpr
  -> m (CoreExpr, CoreExpr)
unifyAndNorm this other = do
  (this', other') <- unifyExprs this other
    ??= "Unable to unify ignore/circuit pair with current/ignore pair"

  instEnv <- getInstEnvs'

  prog <- reader $ mg_binds . modGuts
  let scope = extendInScopeSetBndrs emptyInScopeSet prog

  let instantiateAndNormalize expr = do
          let expr' = resolveInstances instEnv expr
          Lint.panic Lint.base scope expr'
          guts <- reader modGuts
          -- monomorphize guts expr'
          normalize guts expr'

  -- Normalize circuits
  this'' <- instantiateAndNormalize this'
  other'' <- instantiateAndNormalize other'

  pure (this'', other'')

-- TODO: Implement this!
removeUCBinds :: MonadCore m => Pass m ModGuts
removeUCBinds guts = do
  pure guts
