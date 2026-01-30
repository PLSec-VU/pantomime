module Pantomime.Passes
  ( printAndLintPass
  , checkValidityPass
  ) where

import GHC.Plugins hiding (empty, (<>), thNameToGhcName, getFirstAnnotations)
import GHC.Core.Lint
import GHC.Driver.Config.Core.Lint (initLintConfig)

import Grisette
  ( GrisetteSMTConfig (..)
  , SMTConfig (..)
  , Timing (..)
  , z3
  )

import Data.Data (Data)
import Data.Traversable (for)

import Control.Error

import Language.Haskell.TH qualified as TH

import Pantomime.Unification
import Pantomime.Solve
import Pantomime.Axiom (resolvePluginAxioms)
import Pantomime.Annotation

import Effectful
import Effectful.Provider
import Effectful.Grisette.Solver
import Effectful.Exception (throwIO)
import Effectful.Context
import Effectful.Error.Static (Error, CallStack, runErrorWith)
import Effectful.Fail (Fail, runFailIO)
import Effectful.GHC.TH
import Effectful.GHC.CoreE
import Effectful.GHC.DynFlags
import Effectful.GHC.Display
import Effectful.GHC.TyThing
import Effectful.GHC.External
import Effectful.GHC.Annotations

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
-- TODO: We now support recursive functions. We should modify this function to
-- enable running them!
-- | Run the given pass on all binders that have the given annotation.
annBindsPass
  :: forall a es
   . Data a
  => HasAnnotations :> es
  => (a -> CoreBind' -> Eff es CoreBind')
  -> ModGuts
  -> Eff es ModGuts
annBindsPass pass guts = do
  -- TODO: We should probably run every annotation!
  (_, anns) <- getFirstAnnotations @a deserializeWithData

  binds <- for (mg_binds guts) \case
    NonRec x e | Just ann <- lookupUFM anns $ varName x -> do
      nonRec <$> pass ann (Bind' x e)
    b -> pure b

  pure guts { mg_binds = binds }

printAndLintPass
  :: forall a
   . Data a
  => CoreToDo
printAndLintPass = do
  let name = TH.nameBase 'printAndLintPass
  let pass guts = runSymbolic guts $ annBindsPass (const @_ @a printAndLint) guts
  CoreDoPluginPass name pass

-- TODO: I'm not sure if all these effects are actually used anymore. I should
-- make work of checking this at some point!
runSymbolic
  :: HasCallStack
  => ModGuts
  -> Eff
    [ Error (LookupError TH.Name)
    , Error (LookupError Name)
    , Error OversaturatedError
    , Error UnificationError
    , Error SolverError
    , Error ()
    , Provider_ Solver ()
    , HasAnnotations
    , THNameToGHCName
    , HasThings
    , Context Reader CoreProgram
    , Context Reader [TyCon]
    , HasInstEnvs
    , HasFamInstEnvs
    , HasExternalPackageState
    , Display
    , HasDynFlagsE
    , Fail
    , CoreE
    , IOE
    ] a
  -> CoreM a
runSymbolic guts
  = runCoreEM
  . runFailIO
  . runHasDynFlagsE
  . runDisplay
  . runHasExternalPackageState
  . runHasFamInstEnv guts
  . runHasInstEnvs guts
  . runContextReader (mg_tcs guts)
  . runContextReader (mg_binds guts)
  . runHasThings
  . runThNameToGhcName
  . runHasAnnotations guts
  . runProvider_ (const $ runSolver solver)
  . runErrorWith @() propagateErrorShow
  . runErrorWith @SolverError propagateErrorShow
  . runErrorWith @UnificationError propagateError
  . runErrorWith @OversaturatedError propagateError
  . runErrorWith @(LookupError Name) propagateError
  . runErrorWith @(LookupError TH.Name) propagateErrorShow
  where
    -- TODO: We could let the user decide which solver no?
    solver = z3
      { sbvConfig = (sbvConfig z3)
        { verbose = True
        , timing = PrintTiming
        }
      }

    panicDocIO :: String -> SDoc -> Eff es a
    panicDocIO s doc = throwIO $ PprPanic s doc

    propagateError
      :: Outputable o
      => CallStack
      -> o
      -> Eff es a
    propagateError cs doc = panicDocIO "runSymbolic" $ vcat
      [ ppr doc
      , prettyCallStackDoc cs
      ]

    propagateErrorShow
      :: Show s
      => CallStack
      -> s
      -> Eff es a
    propagateErrorShow cs = propagateError cs . text @SDoc . show

-- TODO: Instead of just running a pass per binder, I want to accumulate the
-- results for all checks. In fact, this isn't even a pass as we do not modify
-- the CoreExpr. This is also true for the other 'passes' in this module.
-- TODO: I think the name on this function should be different. It is not really
-- indicative what it checks now. Or at least, the annotation it specialises to.
checkValidityPass :: CoreToDo
checkValidityPass = do
  let name = TH.nameBase 'checkValidityPass
  let pass guts = runSymbolic guts $ annBindsPass checkValidity guts
  CoreDoPluginPass name pass

printAndLint
  :: HasCallStack
  => Context Reader CoreProgram :> es
  => HasDynFlagsE :> es
  => Display :> es
  => CoreBind'
  -> Eff es CoreBind'
printAndLint bind = do
  dflags <- getDynFlags
  let cfg = initLintConfig dflags []
  prog <- get @CoreProgram
  let res = lintCoreBindings' cfg prog
  debug bind
  debug res
  pure bind

checkValidity
  :: HasCallStack
  => Error () :> es
  => Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error SolverError :> es
  => Context Reader CoreProgram :> es
  => Context Reader [TyCon] :> es
  => Provider_ Solver () :> es
  => HasFamInstEnvs :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Theory
  -> CoreBind'
  -> Eff es CoreBind'
-- TODO: The check itself permits recursive binders, so we should not restrict
-- the input here really!
checkValidity (Theory axioms) (Bind' var expr) = do
  axioms' <- resolvePluginAxioms axioms
  checkValid axioms' expr
  pure $ Bind' var expr
