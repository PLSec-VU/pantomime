module UC
  ( plugin
  , UC (..)
  , UCCompare (..)
  , UCNorm (..)
  , UCTactic (..)
  , Projection (..)
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Lint
import GHC.Driver.Config.Core.Lint (initLintConfig)
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
import GHC.Core.Map.Expr (eqCoreExpr)

import GHC.MonadCore
import Data.Maybe (catMaybes)

import Data.Data

import Control.Monad.Reader (ReaderT (..), reader)
import Control.Monad (forM, foldM, unless)

import qualified Language.Haskell.TH.Syntax as TH

import qualified Projection
import Types
import Util
import Transform
import Unification

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

-- TODO: Change printUCGenerated to printAnnotated, which should take a type
-- parameter.
install :: MonadCore m => [CommandLineOption] -> Pass m [CoreToDo]
install _ todo = return $ mconcat
  [ normalizePasses
  , comparePasses
  , tacticPasses
  , todo
  ]
  where
    withProxy proxy ls = (\f -> f proxy) <$> ls

    normalizePasses = withProxy (Proxy @(UCGenerated UCNorm))
      [ createUCBindsPass
      , normalizePass
      , printAndLintPass
      , removeUCBindsPass
      ]

    comparePasses = withProxy (Proxy @(UCGenerated (UCCompare TH.Name)))
      [ createUCBindsPass
      , normalizePass
      , ucComparePass
      , printAndLintPass
      , removeUCBindsPass
      ]

    tacticPasses = withProxy (Proxy @(UCGenerated (UCTactic TH.Name)))
      [ createUCBindsPass
      , projectOutputPass
      , normalizePass
      , checkSProjPass
      , checkIProjPass
      , printAndLintPass
      , removeUCBindsPass
      ]

createUCBinds
  :: forall m a b. (Data a, Data b, MonadFail m, MonadCore m)
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
  :: forall m a. (Data a, MonadCore m)
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
  :: forall a. Data a
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
  :: forall a. Data a
  => Proxy a
  -> CoreToDo
printAndLintPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'printAndLintPass
    pass = annBindsPassWithGuts $ \(_ :: a) -> printAndLint

normalizePass
  :: forall a. Data a
  => Proxy a
  -> CoreToDo
normalizePass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'normalizePass
    pass = annBindsPassWithGuts $ \(_ :: a) -> bindPass normalize

projectOutputPass :: proxy -> CoreToDo
projectOutputPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'projectOutputPass
    pass = annBindsPassWithGuts projectOutput

checkSProjPass :: proxy -> CoreToDo
checkSProjPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'checkSProjPass
    pass = annBindsPassWithGuts checkSProjections

checkIProjPass :: proxy -> CoreToDo
checkIProjPass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'checkIProjPass
    pass = annBindsPassWithGuts checkIProj

ucComparePass :: proxy -> CoreToDo
ucComparePass _ = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'ucComparePass
    pass = annBindsPassWithGuts ucCompare

printAndLint :: MonadCore m => MonadMod m => Pass m CoreBind'
printAndLint bind = do
  dflags <- liftCore getDynFlags
  let cfg = initLintConfig dflags []
  prog <- reader mg_binds
  let res = lintCoreBindings' cfg prog
  dbg bind
  dbg res
  return bind

-- | Project the output of all generated UC binders, according to the
-- observation function in the annotation.
projectOutput :: MonadFail m => MonadCore m => MonadMod m => UCGenerated (UCTactic TH.Name) -> Pass m CoreBind'
projectOutput (UCGenerated uc) (Bind' var expr) = do
  let resolve name = Var <$> resolveTH' name

  oproj <- resolve 'Projection.oproj
  obs <- resolve $ observation uc

  expr' <- occurAnalyseExpr <$> foldM polyApp oproj [obs, expr]
    ??= "Incompatible types on observation/implementation pair"

  let var' = setVarType var $ exprType expr'
  return $ Bind' var' expr'

checkSProjections :: MonadFail m => MonadCore m => MonadMod m => UCGenerated (UCTactic TH.Name) -> Pass m CoreBind'
checkSProjections (UCGenerated uc) bind = foldM (flip checkSProj) bind $ projections uc

checkSProj :: MonadFail m => MonadCore m => MonadMod m => Projection TH.Name -> Pass m CoreBind'
checkSProj projection (Bind' var expr) = do
  let resolve name = Var <$> resolveTH' name

  -- Fetch input projection, leakage and simulator functions
  sproj' <- resolve 'Projection.sproj'
  ign <- resolve $ ignore projection
  circ <- resolve $ circuit projection

  -- Compose ignore with circuit
  ignCirc <- occurAnalyseExpr <$> foldM polyApp sproj' [ign, circ]
    ??= "Incompatible types on ignore/circuit pair"

  -- Compose current with ignore
  sproj <- resolve 'Projection.sproj
  exprIgn <- occurAnalyseExpr <$> foldM polyApp sproj [ign, expr]
    ??= "Incompatible types on current/ignore pair"

  (ignCirc', exprIgn') <- unifyAndNorm ignCirc exprIgn

  -- Check whether they are equal
  unless (exprIgn' `eqCoreExpr` ignCirc') $ do
    dbg' "current/ignore:"
    dbg exprIgn'
    dbg' "ignore/circuit:"
    dbg ignCirc'
    fail "Expression does not equal ignore/circuit pair."

  let var' = setVarType var $ exprType circ
  let bind = Bind' var' circ

  dbg' $ "State projection passed: " <> show projection
  return bind

checkIProj :: MonadFail m => MonadCore m => MonadMod m => UCGenerated (UCTactic TH.Name) -> Pass m CoreBind'
checkIProj (UCGenerated uc) (Bind' var expr) = do
  let resolve name = Var <$> resolveTH' name

  -- Fetch input projection, leakage and simulator functions
  iproj <- resolve 'Projection.iproj
  leak <- resolve $ leakage uc
  sim <- resolve $ simulator uc

  -- Compose leakage with simulator
  leakSim <- occurAnalyseExpr <$> foldM polyApp iproj [leak, sim]
    ??= "Incompatible types on leak/sim pair"

  -- Unify their types so we can compare the circuits.
  (leakSim', expr') <- unifyAndNorm leakSim  expr

  -- Check whether they are equal
  unless (expr' `eqCoreExpr` leakSim') $ do
    dbg' "current:"
    dbg expr'
    dbg' "leakage/simulator:"
    dbg leakSim'
    fail "Expression does not equal leakage/simulator pair."
  
  -- We need to adjust the variable type, since we unified the expressions.
  let var' = setVarType var $ exprType expr'
  return $ Bind' var' expr'

ucCompare :: MonadFail m => MonadCore m => MonadMod m => UCGenerated (UCCompare TH.Name) -> Pass m CoreBind'
ucCompare (UCGenerated (UCCompare other)) (Bind' var expr) = do
  let resolve name = Var <$> resolveTH' name
  other' <- resolve other

  (expr', other'') <- unifyAndNorm expr other'

  -- Check whether they are equal
  unless (expr' `eqCoreExpr` other'') $ do
    dbg expr'
    dbg other''
    fail "Expressions were not equal"
  
  return $ Bind' var expr

unifyAndNorm
  :: MonadFail m
  => MonadCore m
  => MonadMod m 
  => CoreExpr 
  -> CoreExpr 
  -> m (CoreExpr, CoreExpr)
unifyAndNorm this other = do
  (this', other') <- unifyExprs this other
    ??= "Unable to unify ignore/circuit pair with current/ignore pair"

  -- Normalize circuits
  this'' <- occurAnalyseExpr <$> normalize this'
  other'' <- occurAnalyseExpr <$> normalize other'

  return (this'', other'')

-- TODO: Implement this!
removeUCBinds :: MonadCore m => Pass m ModGuts
removeUCBinds guts = do
  return guts
