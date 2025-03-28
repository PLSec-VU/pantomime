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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
-- TODO: I want to remove many of these pragmas, also for the other files. Most
-- of them should just be included in the top-level flags. There also seems to
-- be a lot of obsolete stuff. Perhaps its good to first find out which flags
-- are actually used.

module Symbolic.Solve
  ( NonEq (..)
  , exprSymEq
  ) where

import GHC.Plugins
import GHC.Platform (PlatformWordSize (..), Platform (..))
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Tc.Utils.TcType (eqType, tcSplitSigmaTy)
import GHC.MonadCore

import Grisette.Unified (EvalModeTag (..))
import Grisette
  ( GrisetteSMTConfig (..)
  , SMTConfig (..)
  , Timing (..)
  , Solvable (..)
  , SolvingFailure (..)
  , LogicalOp (..)
  , z3
  , solve
  , indexed
  )

import Control.Monad.Except (MonadError (..), modifyError, runExceptT)
import Control.Monad.State (evalStateT)
import Control.Monad (forM, unless)

import Data.Functor ((<&>))
import Data.Foldable (forM_)

import Symbolic.WordSize
import Symbolic.Evaluate
import Symbolic.Environment
import Symbolic.Value
import Symbolic.Concrete
import Symbolic.Runtime
import Symbolic.MonadEval

-- TODO: Rename this thing.
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
  :: forall m
   . MonadCore m
  => HasDynFlags m
  => CoreExpr
  -> CoreExpr
  -> m (Either NonEq ())
exprSymEq lhs rhs = do
  -- Get the target platform word size.
  dflags <- getDynFlags
  let pwsize = platformWordSize $ targetPlatform dflags

  -- We run the comparison with the word size of the target platform.
  case pwsize of
    PW4 -> exprSymEq' @m @PW4 lhs rhs
    PW8 -> exprSymEq' @m @PW8 lhs rhs

exprSymEq'
  :: forall m ws
   . MonadCore m
  => KnownWordSize ws
  => CoreExpr
  -> CoreExpr
  -> m (Either NonEq ())
exprSymEq' lhs rhs = flip evalStateT (SymbolicState 0) . runExceptT $ do
  unless (exprType lhs `eqType` exprType rhs) $ do
    throwError $ EvalError IllTyped

  (bndrs, lres, rres, eq) <- modifyError EvalError $ do
    bndrs <- symbolicBndrs $ exprType lhs

    let saturate expr = do
          value <- evaluate emptyEnv expr
          applyValues @_ @ws value bndrs

    lresult <- saturate lhs
    rresult <- saturate rhs
    neq <- symNot <$> weakEq lresult rresult
    pure (bndrs, lresult, rresult, neq)

  -- TODO: We could let the user decide which solver no?
  let z3' = z3
        { sbvConfig = (sbvConfig z3)
          { verbose = True
          , timing = PrintTiming
          }
        }

  result <- liftCore . liftIO $ solve z3' eq

  case result of
    Right model -> do
      let concretise' = modifyError EvalError . concretise model
      bndrs' <- forM bndrs concretise'
      lres' <- concretise' lres
      rres' <- concretise' rres
      dbg' "-------------"
      forM_ bndrs' dbg
      dbg' "-------------"
      dbg lres'
      dbg' "=/=/=/=/=/=/="
      dbg rres'
      _ <- error "We crash on non-equal for now."

      throwError $ Counterexample bndrs'
    Left Unsat -> pure ()
    Left err -> throwError $ SolveError err

-- TODO: We have a function to create a fresh typed value now, together with
-- types attached to function values. We should be able to saturate a value
-- without being given its type separately.
symbolicBndrs
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => Type
  -> m [Value m ws]
symbolicBndrs ty = do
  ty' <- case tcSplitSigmaTy ty of
    ([], [], ty') -> pure ty'
    -- TODO: Support polymorphism.
    -- For now, we don't support polymorphism or dictionaries at the top level.
    _ -> throwError UnsupportedExpr

  let (argTys, _) = splitFunTys ty'

  -- Use state monad to track unique identifier for arguments.
  forM argTys $ \argTy -> do
    -- Get next identifier.
    idx <- freshIdx

    -- Create symbolic variable.
    let untyped :: forall c t. Solvable c t => RuntimeValue S t
        untyped = pure . sym $ indexed "!arg" idx

    -- Type the symbolic variable according to the argument type.
    let argTy' = scaledThing argTy
    typedValue untyped argTy'
