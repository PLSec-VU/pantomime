{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
-- TODO: I want to remove many of these pragmas, also for the other files. Most
-- of them should just be included in the top-level flags. There also seems to
-- be a lot of obsolete stuff. Perhaps its good to first find out which flags
-- are actually used.

-- TODO: I feel like the pantomime dependencies that are used solely by the
-- final solver should go under Pantomime.Solve.X (e.g. Pantomime.Solve.Value).
-- Right now, the hierarchy is a bit too flat, which makes the project structure
-- a lot less clear.

module Pantomime.Solve
  ( NonEq (..)
  , exprSymEq
  ) where

import GHC.Plugins
import GHC.Platform (PlatformWordSize (..), Platform (..))
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Core.FamInstEnv (FamInstEnv)
import GHC.Tc.Utils.TcType (eqType, tcSplitSigmaTy)

import Grisette
  ( GrisetteSMTConfig (..)
  , SMTConfig (..)
  , Timing (..)
  , SolvingFailure (..)
  , LogicalOp (..)
  , z3
  , solve
  )

import Control.Monad (forM, unless)

import Data.Functor ((<&>))
import Data.Foldable (forM_)

import Language.Haskell.TH qualified as TH

import Pantomime.WordSize
import Pantomime.Evaluate
import Pantomime.Environment
import Pantomime.Value
import Pantomime.Concrete
import Pantomime.Runtime
import Pantomime.MonadEval

-- TODO: These modules should just get their own package such that a user can
-- just provide the interpretations they require for the code!
import Pantomime.Base
import Pantomime.Clash

import Effectful
import Effectful.Context
import Effectful.Error.Static (Error, throwError_, runErrorNoCallStack, runErrorNoCallStackWith)
import Effectful.Fail
import Effectful.GHC.DynFlags
import Effectful.GHC.Display
import Effectful.Grisette.Fresh
import Effectful.GHC.TyThing
import Effectful.GHC.TH
import Effectful.GHC.External

-- TODO: We really want to remove this thing once we get rid of MonadEval in
-- the entire codebase. This return is a horrible overapproximation!
data NonEq
  -- TODO: It would be nice if the counterexample also included the final
  -- result. Even if just for checking whether the output is actually correct!
  = Counterexample [Concrete]
  | EvalError EvalError
  -- TODO: Add in the actualy solver error. We don't want to directly copy the
  -- solver result, as Unsat shows validity on our case.
  | SolveError SolvingFailure

instance Outputable NonEq where
  ppr = \case
    Counterexample values -> vcat $ values <&> ppr
    EvalError err -> text "eval-error: " <+> ppr err
    SolveError err -> text "solver error: " <+> text (show err)

exprSymEq
  :: forall es
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Context Reader ModGuts :> es
  => Context Reader FamInstEnv :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => ExtFamInstEnv :> es
  => IOE :> es
  => Fail :> es
  => Display :> es
  => HasDynFlagsE :> es
  => CoreExpr
  -> CoreExpr
  -> Eff es (Either NonEq ())
exprSymEq lhs rhs = do
  -- Get the target platform word size.
  dflags <- getDynFlags
  let pwsize = platformWordSize $ targetPlatform dflags

  -- We run the comparison with the word size of the target platform.
  case pwsize of
    PW4 -> exprSymEq' @PW4 lhs rhs
    PW8 -> exprSymEq' @PW8 lhs rhs

exprSymEq'
  :: forall ws es
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Context Reader ModGuts :> es
  => Context Reader FamInstEnv :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => ExtFamInstEnv :> es
  => IOE :> es
  => Fail :> es
  => Display :> es
  => KnownWordSize ws
  => CoreExpr
  -> CoreExpr
  -> Eff es (Either NonEq ())
exprSymEq' lhs rhs = runErrorNoCallStack @NonEq $ runFresh "fresh" do
  let lty = exprType lhs
  let rty = exprType rhs
  unless (lty `eqType` rty) $ do
    throwError_ $ EvalError IllTyped

  let runEvalErr = runErrorNoCallStackWith $ throwError_ . EvalError

  (bndrs, lres, rres, eq) <- runEvalErr do
    bndrs <- symbolicBndrs $ exprType lhs

    base <- baseValues
    clash <- clashInterp
    env <- extendManyEnv emptyEnv $ base ++ clash

    prog <- gets @ModGuts mg_binds
    let env' = extendLocalEnv env prog

    let saturate expr = do
          value <- evaluate env' expr
          applyValues @_ @ws value bndrs

    lresult <- saturate lhs
    rresult <- saturate rhs
    eq <- weakEq lresult rresult
    pure (bndrs, lresult, rresult, eq)

  -- TODO: We could let the user decide which solver no?
  let z3' = z3
        { sbvConfig = (sbvConfig z3)
          { verbose = True
          , timing = PrintTiming
          }
        }

  -- TODO: This should be an effect. We really want to get rid of the IO effect.
  result <- liftIO $ solve z3' (symNot eq)

  case result of
    Right model -> do
      let concretise' = runEvalErr . concretise model
      bndrs' <- forM bndrs concretise'
      lres' <- concretise' lres
      rres' <- concretise' rres
      debugS "-------------"
      forM_ bndrs' debug
      debugS "-------------"
      debug lres'
      debugS "=/=/=/=/=/=/="
      debug rres'
      _ <- fail "We crash on non-equal for now."

      throwError_ $ Counterexample bndrs'
    Left Unsat -> pure ()
    Left err -> throwError_ $ SolveError err

-- TODO: We have a function to create a fresh typed value now, together with
-- types attached to function values. We should be able to saturate a value
-- without being given its type separately.
symbolicBndrs
  :: forall ws es
   . Error EvalError :> es
  => Context Reader FamInstEnv :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => Fresh :> es
  => ExtFamInstEnv :> es
  => KnownWordSize ws
  => Type
  -> Eff es [Value (Eff es) ws]
symbolicBndrs ty = do
  ty' <- case tcSplitSigmaTy ty of
    ([], [], ty') -> pure ty'
    -- TODO: Support polymorphism.
    -- For now, we don't support polymorphism or dictionaries at the top level.
    -- Do we really not at this point? I'll have to verify it!
    _ -> throwError_ UnsupportedExpr

  let (argTys, _) = splitFunTys ty'

  forM argTys \argTy -> do
    -- Type the symbolic variable according to the argument type.
    let argTy' = scaledThing argTy
    evalFresh (argTy', Right @RuntimeError ())
