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
import Control.Monad.State (evalStateT, MonadState (..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad (forM, unless)

import Data.Functor ((<&>))

import Symbolic.KnownPos
import Symbolic.Evaluate
import Symbolic.Environment
import Symbolic.ADT
import Symbolic.Util
import Symbolic.Value
import Symbolic.Concrete
import Symbolic.Runtime
import Data.Foldable (forM_)

-- TODO: Rename this thing.
data NonEq
  -- TODO: It would be nice if the counterexample also included the final
  -- result. Even if just for checking whether the output is actually correct!
  = Counterexample [Concrete]
  | EvalError EvalError
  -- TODO: Add in the actualy solver error. We don't want to directly copy the
  -- solver result, as Unsat shows validity on our case.
  | SolveError

instance Outputable NonEq where
  ppr = \case
    Counterexample values -> vcat $ values <&> ppr
    EvalError err -> text "eval-error: " <+> ppr err
    -- TODO: More details what failed for the solver!
    SolveError -> text "solver error"

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
    PW4 -> exprSymEq' @m @32 lhs rhs
    PW8 -> exprSymEq' @m @64 lhs rhs

exprSymEq'
  :: forall m n
   . MonadCore m
  => KnownPos n
  => CoreExpr
  -> CoreExpr
  -> m (Either NonEq ())
exprSymEq' lhs rhs = runExceptT $ do
  dbg lhs
  unless (exprType lhs `eqType` exprType rhs) $ do
    throwError $ EvalError IllTyped

  let st = SymbolicState
        { nextIdx = 0
        }

  (bndrs, lres, rres, eq) <- flip evalStateT st . modifyError EvalError $ do
    bndrs <- symbolicBndrs $ exprType lhs

    let saturate expr = do
          value <- evaluate @_ @n emptyEnv expr
          applyValues @_ @n value bndrs

    lresult <- saturate lhs
    rresult <- saturate rhs
    eq <- assertEq lresult rresult
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
      let concretize' = modifyError EvalError . concretize model
      bndrs' <- forM bndrs concretize'
      lres' <- concretize' lres
      rres' <- concretize' rres
      forM_ bndrs' dbg
      dbg' "-------------"
      dbg lres'
      dbg' "=/=/=/=/=/=/="
      dbg rres'
      _ <- error "We crash on non-equal for now."

      throwError $ Counterexample bndrs'
    Left Unsat -> pure ()
    Left _ -> throwError $ SolveError

-- FIXME: I don't think this works for divide by zero. I.e. if only one of the
-- two expressions fail, it should be non-equal.
assertEq
  :: forall m n
   . MonadError EvalError m
  => MonadCore m
  => KnownPos n
  => Value m n
  -> Value m n
  -> m (RuntimeValue SymBool)
assertEq = curry $ \case
  (Primitive lhs, Primitive rhs) -> cmpPrimitive lhs rhs
  (ADT lty lhs, ADT rty rhs) -> do
    -- Ensure the equality is sound.
    unless (lty `eqType` rty) $ throwError IllTyped

    -- Gather type info.
    (tyCon, tyArgs) <- whyFail IllTyped $ splitTyConApp_maybe lty
    let dataCons = tyConDataCons tyCon

    -- Gather the branches for each DataCon this ADT could be. This is a pair of
    -- conditional (i.e. the DataCon matches) and the inner assertion.
    branches <- forM dataCons $ \dataCon -> do
      -- Ensure that both ADTs match the current DataCon.
      let inBranch adt = adtIsDataCon @n adt dataCon
      let conditional = mrgLiftA2 (.&&) (inBranch lhs) (inBranch rhs)

      -- Gather the field names.
      let names = dataConAccessorNames dataCon
      let tys = scaledThing <$> dataConInstArgTys dataCon tyArgs
      let accessors = zip names tys

      -- Assertion for every field that they are equal.
      assertions <- forM accessors $ \(name, ty) -> do
        lfield <- accessField' @_ @n lhs name ty
        rfield <- accessField' rhs name ty
        assertEq lfield rfield

      -- Fold the assertions per-field into a single conjunct.
      let assertion = foldl' (mrgLiftA2 (.&&)) (pure true) assertions

      -- TODO: Maybe this should go somewhere else? Is there not a standard
      -- function for this?
      let implies x y = symNot x .|| y

      -- If the tags match, then the fields should also match.
      pure $ mrgLiftA2 implies conditional assertion

    -- Ensure the tags are actually equal.
    let eqTag = cmpRuntime (accessTag @n lhs) (accessTag rhs)

    -- Merge the branches as a large if-then-else.
    pure $ foldl' (mrgLiftA2 (.&&)) eqTag branches

  (Cast' lco lhs, Cast' rco rhs) -> do
    unless (lco `eqCoercion` rco) $ throwError IllTyped
    assertEq lhs rhs

  (Ty lhs, Ty rhs) -> pure . pure . con $ lhs `eqType` rhs
  (Co lhs, Co rhs) -> pure . pure . con $ lhs `eqCoercion` rhs
  (Fun _, Fun _) -> throwError UnsupportedExpr
  _ -> throwError IllTyped

-- FIXME: We should restrict ADT tags to actually be in range of their tag here!
symbolicBndrs
  :: forall m n
   . MonadError EvalError m
  => KnownPos n
  => Type
  -> m [Value m n]
symbolicBndrs ty = do
  ty' <- case tcSplitSigmaTy ty of
    ([], [], ty') -> pure ty'
    -- TODO: Support polymorphism.
    -- For now, we don't support polymorphism or dictionaries at the top level.
    _ -> throwError UnsupportedExpr

  let (argTys, _) = splitFunTys ty'

  -- Use state monad to track unique identifier for arguments.
  flip evalStateT 0 . forM argTys $ \argTy -> do
    -- Get next identifier.
    idx <- state (\s -> let s' = s + 1 in (s, s'))

    -- Create symbolic variable.
    let symbolic :: Solvable c t => RuntimeValue t
        symbolic = pure . sym $ indexed "!arg" idx

    -- Type the symbolic variable according to the argument type.
    let argTy' = scaledThing argTy
    lift $ typedValue symbolic argTy'
