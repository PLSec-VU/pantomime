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
  ( SymBool
  , LogicalOp (..)
  , GrisetteSMTConfig (..)
  , SMTConfig (..)
  , Timing (..)
  , Solvable (..)
  , SolvingFailure (..)
  , z3
  , solveExcept
  , mrgLiftA2
  , indexed
  )

import Control.Monad.Except (MonadError (..), modifyError, runExceptT)
import Control.Monad.State (evalStateT)
import Control.Monad (forM, unless)

import Data.Functor ((<&>))

import Symbolic.WordSize
import Symbolic.Evaluate
import Symbolic.Environment
import Symbolic.ADT
import Symbolic.Util
import Symbolic.Value
import Symbolic.Concrete
import Symbolic.Runtime
import Data.Foldable (forM_)
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
    -- TODO: Unsat is not an error in this case, so we should not return it as
    -- a possible outcome.
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
    eq <- unRuntimeValue <$> assertEq lresult rresult
    pure (bndrs, lresult, rresult, eq)

  -- TODO: We could let the user decide which solver no?
  let z3' = z3
        { sbvConfig = (sbvConfig z3)
          { verbose = True
          , timing = PrintTiming
          }
        }

  -- result <- liftCore . liftIO $ solve z3' eq
  let translate = \case
        Left Invalid -> false
        Right val -> symNot val
        _ -> false

  result <- liftCore . liftIO $ solveExcept z3' translate eq
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

-- FIXME: I don't think this works for divide by zero. I.e. if only one of the
-- two expressions fail, it should be non-equal.
assertEq
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => Value m ws
  -> Value m ws
  -> m (RuntimeValue S SymBool)
assertEq = curry $ \case
  (Primitive lhs, Primitive rhs) -> evalEq lhs rhs
  (Data lhs, Data rhs) -> do
    -- Ensure the equality is sound.
    unless (lhs `eqTyADT` rhs) $ throwError IllTyped

    -- Gather type info.
    let ADT tyCon tyArgs _ = lhs
    let dataCons = tyConDataCons tyCon

    -- Gather the branches for each DataCon this ADT could be. This is a pair of
    -- conditional (i.e. the DataCon matches) and the inner assertion.
    branches <- forM dataCons $ \dataCon -> do
      -- Ensure that both ADTs match the current DataCon.
      let inBranch adt = adtIsDataCon @ws adt dataCon
      conditional <- whyFail IllTyped $ do
        lhs' <- inBranch lhs
        rhs' <- inBranch rhs
        pure $ mrgLiftA2 (.&&) lhs' rhs'

      -- Gather the field names.
      let names = dataConAccessorNames dataCon
      let tys = scaledThing <$> dataConInstArgTys dataCon tyArgs
      let accessors = zip names tys

      -- Assertion for every field that they are equal.
      assertions <- forM accessors $ \(name, ty) -> do
        lfield <- accessField lhs name ty
        rfield <- accessField rhs name ty
        assertEq @m @ws lfield rfield

      -- Fold the assertions per-field into a single conjunct.
      let assertion = foldl' (mrgLiftA2 (.&&)) (pure true) assertions

      -- TODO: Maybe this should go somewhere else? Is there not a standard
      -- function for this?
      let implies x y = symNot x .|| y

      -- If the tags match, then the fields should also match.
      pure $ mrgLiftA2 implies conditional assertion

    -- Ensure the tags are actually equal and valid.
    eqTag <- evalEq (accessTag @ws lhs) (accessTag rhs)

    -- Merge the branches as a large if-then-else.
    pure $ foldl' (mrgLiftA2 (.&&)) eqTag branches
  (Cast' lco lhs, Cast' rco rhs) -> do
    unless (lco `eqCoercion` rco) $ throwError IllTyped
    assertEq lhs rhs

  (Fun lty lhs, Fun rty rhs) -> do
    unless (lty `eqType` rty) $ throwError IllTyped
    arg <- freshValue lty
    lhs' <- lhs arg
    rhs' <- rhs arg
    assertEq lhs' rhs'

  (Ty lhs, Ty rhs) -> pure . pure . con $ lhs `eqType` rhs
  (Co lhs, Co rhs) -> pure . pure . con $ lhs `eqCoercion` rhs
  _ -> throwError IllTyped

-- FIXME: We should restrict ADT tags to actually be in range of their tag here!
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
