module UC
  ( plugin
  , UC (..)
  , UCCompare (..)
  , UCNorm (..)
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

composeImpl
  :: MonadFail m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
  => UC TH.Name
  -> Pass m CoreExpr
composeImpl uc expr = do
  let resolve name = Var <$> resolveTH' name
  let polyApp3 x y z = polyApp x y >>= flip polyApp z

  oproj <- resolve 'Projection.oproj
  obs <- resolve $ observation uc

  sproj <- resolve 'Projection.sproj
  proj <- resolve $ projection uc

  expr' <- polyApp3 oproj obs expr
    ??= "Incompatible types on observation/implementation pair"

  expr'' <- polyApp3 sproj proj expr'
    ??= "Incompatible types on (implementation/observation)/projection pair"

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
  let polyApp3 x y z = polyApp x y >>= flip polyApp z

  sim <- resolve $ simulator uc

  iproj <- resolve 'Projection.iproj
  leak <- resolve $ leakage uc

  sproj' <- resolve 'Projection.sproj'
  proj <- resolve $ projection uc

  expr' <- polyApp3 iproj leak sim
    ??= "Incompatible types on leakage/simulator pair"

  expr'' <- polyApp3 sproj' proj expr'
    ??= "Incompatible types on projection/(leakage/simulator) pair"

  pure $ occurAnalyseExpr expr''

ucCheck
  :: MonadFail m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
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
    dbg' "simulator"
    dbg sim'
    fail "Implementation does not equal simulator"

  let var' = setVarType var $ exprType expr''
  pure $ Bind' var' expr''

ucCompare
  :: MonadFail m
  => MonadCore m
  => MonadReader r m
  => HasModGuts r
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
  => CoreExpr
  -> CoreExpr
  -> m (CoreExpr, CoreExpr)
unifyAndNorm this other = do
  (this', other') <- unifyExprs this other
    ??= "Unable to unify ignore/circuit pair with current/ignore pair"

  -- Normalize circuits
  this'' <- occurAnalyseExpr <$> normalize this'
  other'' <- occurAnalyseExpr <$> normalize other'

  pure (this'', other'')

-- TODO: Implement this!
removeUCBinds :: MonadCore m => Pass m ModGuts
removeUCBinds guts = do
  pure guts
