{-# LANGUAGE AllowAmbiguousTypes #-}

module Pantomime.Passes
  ( printAndLintPass
  , symComparePass
  , checkSpecPass
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

import qualified Projection
import Types
import Util
import Unification
import Pantomime.Solve
import Pantomime.Annotation

-- | An always non-recursive binder.
data Bind' a = Bind' a (Expr a)

-- | Transform an always non-recursive binder into a normal binder.
nonRec :: Bind' a -> Bind a
nonRec (Bind' x e) = NonRec x e

instance OutputableBndr a => Outputable (Bind' a) where
  ppr (Bind' x e) = ppr $ NonRec x e

-- | A core binder that is non-recursive.
type CoreBind' = Bind' CoreBndr

-- | A pass transforms some value of type a inside of monad m.
type Pass m a = a -> m a

-- TODO: These passes do not modify the code. Should we make this less general
-- on the modification side?
--
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

-- | Lint an expression and panic on failure.
lintPanic
  :: HasDynFlags m
  => Monad m
  => InScopeSet
  -> CoreExpr
  -> m ()
lintPanic (InScope vars) expr = do
  dflags <- getDynFlags
  let vars' = nonDetEltsUniqSet vars
  let cfg = initLintConfig dflags vars'
  let result = lintExpr cfg expr
  case result of
    Nothing -> pure ()
    Just err -> pprPanic "Panic on linter warnings/errors" $ vcat
      [ ppr expr
      , ppr vars
      , ppr err
      ]

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
-- TODO: I think the name on this function should be different. It is not really
-- indicative what it checks now.
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
  => Pantomime TH.Name
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
  => Pantomime TH.Name
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
  => Pantomime TH.Name
  -> Pass m CoreBind'
checkSpec spec (Bind' var expr) = do
  guts <- modGuts'
  let program = mg_binds guts
  let scope = extendInScopeSetBndrs emptyInScopeSet program

  imp <- composeImpl spec expr
  lintPanic scope imp

  sim <- composeSim spec
  lintPanic scope sim

  (imp', sim') <- unifyExprs imp sim
    ??= "Unable to unify implementation projection with simulator"

  instEnvs <- getInstEnvs'
  let imp'' = resolveInstances instEnvs imp'
  let sim'' = resolveInstances instEnvs sim'

  lintPanic scope imp''
  lintPanic scope sim''

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
