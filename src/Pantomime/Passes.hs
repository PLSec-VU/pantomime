module Pantomime.Passes
  ( printAndLintPass
  , symComparePass
  , checkSpecPass
  ) where

import GHC.Plugins hiding (empty, (<>), thNameToGhcName)
import GHC.Core.Lint
import GHC.Core.Opt.OccurAnal (occurAnalyseExpr)
import GHC.Core.InstEnv (InstEnv)
import GHC.Unit.Module.Deps (Dependencies)
import GHC.Driver.Config.Core.Lint (initLintConfig)

import Data.Data

import Control.Monad (forM)
import Control.Error

import Language.Haskell.TH qualified as TH

import Pantomime.Combinator qualified as Combinator
import Pantomime.Unification
import Pantomime.Solve
import Pantomime.Annotation

import Effectful
import Effectful.Context
import Effectful.Error.Static (Error, CallStack, runErrorWith)
import Effectful.Fail (Fail, runFailIO)
import Effectful.GHC.TH
import Effectful.GHC.ModGuts
import Effectful.GHC.CoreE
import Effectful.GHC.DynFlags
import Effectful.GHC.Display
import Effectful.GHC.TyThing
import Effectful.GHC.External
import GHC.Core.FamInstEnv (FamInstEnv)

resolveTH
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Context Reader CoreProgram :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => TH.Name
  -> Eff es Id
resolveTH th = do
  ghc <- thNameToGhcName th
  result <- lookupIdAll ghc
  pure result

-- | An always non-recursive binder.
data Bind' a = Bind' a (Expr a)

-- | Transform an always non-recursive binder into a normal binder.
nonRec :: Bind' a -> Bind a
nonRec (Bind' x e) = NonRec x e

instance OutputableBndr a => Outputable (Bind' a) where
  ppr (Bind' x e) = ppr $ NonRec x e

-- | A core binder that is non-recursive.
type CoreBind' = Bind' CoreBndr

-- TODO: We should require annotations in the effect environment to do the
-- lookup for the mod guts. The pass actually only modifies the binds.
-- TODO: These passes do not modify the code. Should we make this less general
-- on the modification side? It seems to me like we should have them return a
-- unit?
-- | Run the given pass on all binders that have the given annotation.
annBindsPass
  :: forall a es
   . Data a
  => IOE :> es
  => CoreE :> es
  => (a -> CoreBind' -> Eff es CoreBind')
  -> ModGuts
  -> Eff es ModGuts
annBindsPass pass guts = do
  -- TODO: We should probably run every annotation!
  (_, anns) <- liftCore $ getFirstAnnotations @a deserializeWithData guts

  binds <- forM (mg_binds guts) $ \case
    NonRec x e | Just ann <- lookupUFM anns $ varName x -> do
      nonRec <$> pass ann (Bind' x e)
    b -> pure b

  pure guts { mg_binds = binds }

-- | Lint an expression and panic on failure.
lintPanic
  :: HasDynFlagsE :> es
  => InScopeSet
  -> CoreExpr
  -> Eff es ()
lintPanic (InScope vars) expr = do
  dflags <- getDynFlags
  -- I think the in-scope set could also just come from the CoreProgram?
  let vars' = nonDetEltsUniqSet vars
  let cfg = initLintConfig dflags vars'
  let result = lintExpr cfg expr
  case result of
    Nothing -> pure ()
    -- TODO: This should probably not panic but just throw?
    Just err -> pprPanic "Panic on linter warnings/errors" $ vcat
      [ ppr expr
      , ppr vars
      , ppr err
      ]

printAndLintPass
  :: forall a
   . Data a
  => CoreToDo
printAndLintPass = do
  let name = TH.nameBase 'printAndLintPass
  let pass guts = runModGuts guts $ annBindsPass (const @_ @a printAndLint) guts
  CoreDoPluginPass name $ runCoreEM . runDisplay . pass

runSymbolic
  :: HasCallStack
  => Eff
    [ Error (LookupError TH.Name)
    , Error (LookupError Name)
    , Error OversaturatedError
    , Error UnificationError
    , THNameToGHCName
    , HasThings
    , ExtInstEnv
    , ExtFamInstEnv
    , ExtPackages
    , Display
    , HasDynFlagsE
    , Fail
    , CoreE
    , IOE
    ] a
  -> CoreM a
runSymbolic
  = runCoreEM
  . runFailIO
  . runHasDynFlagsE
  . runDisplay
  . runExtPackages
  . runExtAll
  . runHasThings
  . runThNameToGhcName
  . runErrorWith @UnificationError propagateError
  . runErrorWith @OversaturatedError propagateError
  . runErrorWith @(LookupError Name) propagateError
  . runErrorWith @(LookupError TH.Name) propagateErrorShow
  where
    panicDocIO :: IOE :> es => String -> SDoc -> Eff es a
    panicDocIO s doc = liftIO . throwGhcExceptionIO $ PprPanic s doc

    propagateError
      :: IOE :> es
      => Outputable o
      => CallStack
      -> o
      -> Eff es a
    propagateError cs doc = panicDocIO "runSymbolic" $ vcat
      [ ppr doc
      , prettyCallStackDoc cs
      ]

    propagateErrorShow cs s = propagateError cs $ text @SDoc (show s)

symComparePass :: CoreToDo
symComparePass = do
  let name = TH.nameBase 'symComparePass
  let pass guts = runModGuts guts $ annBindsPass symCompare guts
  CoreDoPluginPass name $ runSymbolic . pass

-- TODO: Instead of just running a pass per binder, I want to accumulate the
-- results for all checks. In fact, this isn't even a pass as we do not modify
-- the CoreExpr. This is also true for the other 'passes' in this module.
-- TODO: I think the name on this function should be different. It is not really
-- indicative what it checks now.
checkSpecPass :: CoreToDo
checkSpecPass = do
  let name = TH.nameBase 'checkSpecPass
  let pass guts = runModGuts guts $ annBindsPass checkSpec guts
  CoreDoPluginPass name $ runSymbolic . pass

printAndLint
  :: HasCallStack
  => Context Reader ModGuts :> es
  => IOE :> es
  => CoreE :> es
  => Display :> es
  => CoreBind'
  -> Eff es CoreBind'
printAndLint bind = do
  dflags <- liftCore getDynFlags
  let cfg = initLintConfig dflags []
  prog <- gets mg_binds
  let res = lintCoreBindings' cfg prog
  debug bind
  debug res
  pure bind

composeImpl
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error UnificationError :> es
  => Error OversaturatedError :> es
  => Context Reader CoreProgram :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => Pantomime TH.Name
  -> CoreExpr
  -> Eff es CoreExpr
composeImpl spec expr = do
  let resolve name = Var <$> resolveTH name

  compose <- resolve 'Combinator.composeI

  obs <- resolve $ observation spec
  proj <- resolve $ projection spec

  expr' <- unifyApps compose [expr, obs, proj]

  pure $ occurAnalyseExpr expr'

composeSim
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error UnificationError :> es
  => Error OversaturatedError :> es
  => Context Reader CoreProgram :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => Pantomime TH.Name
  -> Eff es CoreExpr
composeSim uc = do
  let resolve name = Var <$> resolveTH name

  compose <- resolve 'Combinator.composeS

  sim <- resolve $ simulator uc
  leak <- resolve $ leakage uc
  proj <- resolve $ projection uc

  expr' <- unifyApps compose [leak, sim, proj]

  pure $ occurAnalyseExpr expr'

checkSpec
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error UnificationError :> es
  => Error OversaturatedError :> es
  => Context Reader CoreProgram :> es
  => Context Reader InstEnv :> es
  => Context Reader FamInstEnv :> es
  => Context Reader Dependencies :> es
  => Context Reader ModGuts :> es
  => IOE :> es
  => Fail :> es
  => Display :> es
  => ExtInstEnv :> es
  => ExtFamInstEnv :> es
  => HasDynFlagsE :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Pantomime TH.Name
  -> CoreBind'
  -> Eff es CoreBind'
checkSpec spec (Bind' var expr) = do
  program <- get @CoreProgram
  let scope = extendInScopeSetBndrs emptyInScopeSet program

  imp <- composeImpl spec expr
  lintPanic scope imp

  sim <- composeSim spec
  lintPanic scope sim

  (imp', sim') <- unifyExprs imp sim

  imp'' <- resolveInstances imp'
  sim'' <- resolveInstances sim'

  lintPanic scope imp''
  lintPanic scope sim''

  result <- exprSymEq imp'' sim''

  case result of
    Right _ -> do
      debugS "Expressions are equal!"
    Left err -> do
      debug err
      fail "Expressions are **NOT** equal"

  pure $ Bind' var expr

symCompare
  :: HasCallStack
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Context Reader CoreProgram :> es
  => Context Reader FamInstEnv :> es
  => Context Reader ModGuts :> es
  => IOE :> es
  => Fail :> es
  => Display :> es
  => ExtFamInstEnv :> es
  => HasDynFlagsE :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => SymCompare TH.Name
  -> CoreBind'
  -> Eff es CoreBind'
symCompare (SymCompare other) (Bind' var expr) = do
  let resolve name = Var <$> resolveTH name

  other' <- resolve other

  result <- exprSymEq expr other'

  case result of
    Right _ -> do
      debugS "Expressions were equal!"
      pure $ Bind' var expr
    Left err -> do
      debug err
      fail "Expressions were not equal"
