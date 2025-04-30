{-# LANGUAGE AllowAmbiguousTypes #-}
module UC
  ( plugin
  , SymCompare (..)
  , Spec (..)
  , Projection.Circuit
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Lint
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
import GHC.Driver.Config.Core.Lint (initLintConfig)
import GHC.MonadCore

import Data.Data

import Control.Monad.Reader (MonadReader, ReaderT (..), reader)
import Control.Monad (forM)

import qualified Language.Haskell.TH.Syntax as TH

import qualified Lint
import qualified Projection
import Types
import Util
import Unification
import Pantomime.Solve

plugin :: Plugin
plugin = defaultPlugin
  { installCoreToDos = install
  , pluginRecompile = purePlugin
  }

install :: MonadCore m => [CommandLineOption] -> Pass m [CoreToDo]
install _ todo = pure $ mconcat
  [ symComparePasses
  , checkSpecPasses
  , todo
  ]
  where
    symComparePasses =
      [ printAndLintPass @(SymCompare TH.Name)
      , symComparePass
      ]

    -- TODO: I don't really need to create new binds to do this pass, since I'm
    -- not modifying the binds anyway. Same for the other symbolic check
    -- actually!
    checkSpecPasses =
      [ printAndLintPass @(Spec TH.Name)
      , checkSpecPass
      ]

-- | Run the given pass on all binders that have the given annotation.
annBindsPass
  :: forall m a
   . Data a
  => MonadCore m
  => (a -> Pass m CoreBind')
  -> Pass m ModGuts
annBindsPass pass guts = do
  -- TODO: We should probably run every annotation!
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

printAndLintPass
  :: forall a
   . Data a
  => CoreToDo
printAndLintPass = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'printAndLintPass
    pass = annBindsPassWithGuts $ \(_ :: a) -> printAndLint

symComparePass :: CoreToDo
symComparePass = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'symComparePass
    pass = annBindsPassWithGuts symCompare

-- TODO: Instead of just running a pass per binder, I want to accumulate the
-- results for all checks. In fact, this isn't even a pass as we do not modify
-- the CoreExpr.
checkSpecPass :: CoreToDo
checkSpecPass = CoreDoPluginPass name pass
  where
    name = TH.nameBase 'checkSpecPass
    pass = annBindsPassWithGuts checkSpec

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
  => HasModGuts' m
  => Spec TH.Name
  -> Pass m CoreExpr
composeImpl spec expr = do
  let resolve name = Var <$> resolveTH' name

  compose <- resolve 'Projection.compose
  obs <- resolve $ observation spec

  expr' <- unifyApps compose [expr, obs]
    ??= "Incompatible types on observation/implementation pair"

  sproj <- resolve 'Projection.sproj
  proj <- resolve $ projection spec

  expr'' <- unifyApps sproj [proj, expr']
    ??= "Incompatible types on (implementation/observation)/projection pair"

  pure $ occurAnalyseExpr expr''

composeSim
  :: MonadFail m
  => MonadCore m
  => HasModGuts' m
  => Spec TH.Name
  -> m CoreExpr
composeSim uc = do
  let resolve name = Var <$> resolveTH' name

  compose <- resolve 'Projection.compose
  sproj' <- resolve 'Projection.sproj'

  sim <- resolve $ simulator uc
  leak <- resolve $ leakage uc
  proj <- resolve $ projection uc

  expr' <- unifyApps compose [leak, sim]
    ??= "Incompatible types on leakage/simulator pair"

  expr'' <- unifyApps sproj' [proj, expr']
    ??= "Incompatible types on projection/(leakage/simulator) pair"

  pure $ occurAnalyseExpr expr''

checkSpec
  :: MonadFail m
  => MonadCore m
  => HasModGuts' m
  => HasDynFlags m
  => Spec TH.Name
  -> Pass m CoreBind'
checkSpec spec (Bind' var expr) = do
  guts <- modGuts'
  let program = mg_binds guts
  let scope = extendInScopeSetBndrs emptyInScopeSet program

  imp <- composeImpl spec expr
  Lint.panic Lint.base scope imp

  sim <- composeSim spec
  Lint.panic Lint.base scope sim

  (imp', sim') <- unifyExprs imp sim
    ??= "Unable to unify implementation projection with simulator"

  instEnvs <- getInstEnvs'
  let imp'' = resolveInstances instEnvs imp'
  let sim'' = resolveInstances instEnvs sim'

  Lint.panic Lint.base scope imp''
  Lint.panic Lint.base scope sim''

  result <- exprSymEq imp'' sim''

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
  => HasModGuts' m
  => HasDynFlags m
  => SymCompare TH.Name
  -> Pass m CoreBind'
symCompare (SymCompare other) (Bind' var expr) = do
  let resolve name = Var <$> resolveTH' name

  other' <- resolve other

  result <- exprSymEq expr other'

  case result of
    Right _ -> do
      dbg' "Expressions were equal!"
      pure $ Bind' var expr
    Left err -> do
      dbg err
      fail "Expressions were not equal"
