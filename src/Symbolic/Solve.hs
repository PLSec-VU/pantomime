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

module Symbolic.Solve
  ( NonEq (..)
  , exprSymEq
  ) where

import GHC.Plugins
import GHC.Platform (PlatformWordSize (..), Platform (..))
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Core.Map.Expr (TrieMap(..))
import GHC.Tc.Utils.TcType (eqType)
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
  )

import Control.Monad.Except (MonadError (..), modifyError, runExceptT)
import Control.Monad.State (evalStateT)
import Control.Monad (forM, unless)

import Data.Functor ((<&>))
import Data.String (IsString(..))

import Symbolic.KnownPos
import Symbolic.Evaluate
import Symbolic.ADT
import Symbolic.Util
import Symbolic.Value
import Symbolic.Concrete
import Symbolic.Runtime

-- TODO: Rename this thing.
data NonEq
  -- TODO: It would be nice if the counterexample also included the final
  -- result. Even if just for checking whether the output is actually correct!
  = Counterexample [Concrete]
  | EvalError SymbolicError
  | SolveError

instance Outputable NonEq where
  ppr = \case
    Counterexample values -> vcat $ values <&> ppr
    EvalError err -> text "eval-error: " <+> ppr err
    -- TODO: More details what failed for the solver!
    SolveError -> text "solver error"

exprSymEq
  :: forall m
   . MonadFail m
  => MonadCore m
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
   . MonadFail m
  => MonadCore m
  => KnownPos n
  => CoreExpr
  -> CoreExpr
  -> m (Either NonEq ())
exprSymEq' lhs rhs = runExceptT $ do
  let st = SymbolicState
        { nextIdx = 0
        }

  (bndrs, lres, rres, eq) <- flip evalStateT st . modifyError EvalError $ do
    bndrs <- symbolicBndrs lhs

    let saturate expr = do
          value <- evaluate @_ @n emptyTM expr
          applyValues @_ @n value bndrs

    lresult <- saturate lhs
    rresult <- saturate rhs

    dbg lhs
    case lresult of
      ADT ty val -> do
        dbg ty
        dbg' $ show val
      _ -> pure ()

    dbg rhs
    case rresult of
      ADT ty val -> do
        dbg ty
        dbg' $ show val
      _ -> pure ()

    eq <- assertEq lresult rresult
    pure (bndrs, lresult, rresult, eq)

  dbg' $ show eq

  -- TODO: We could let the user decide which solver no?
  let z3' = z3
        { sbvConfig = (sbvConfig z3)
          { verbose = True
          , timing = PrintTiming
          }
        }

  -- TODO: We should translate the model to our version!
  -- result <- liftCore . liftIO $ solve z3' eq
  let translate = \case
        Left Invalid -> false
        Right val -> symNot val
        _ -> false

  result <- liftCore . liftIO $ solveExcept z3' translate eq
  case result of
    Right model -> do
      let concreteValue' = modifyError EvalError . concretize model
      bndrs' <- forM bndrs concreteValue'
      lres' <- concreteValue' lres
      rres' <- concreteValue' rres
      dbg' "============="
      dbg' $ show model
      dbg' "-------------"
      dbg bndrs'
      dbg' "*************"
      dbg lres'
      dbg' "@@@@@@@@@@@@@"
      dbg rres'
      dbg' "ignore after this for now!"


      throwError $ Counterexample bndrs'
    Left Unsat -> pure ()
    Left _ -> throwError $ SolveError

-- FIXME: I don't think this works for divide by zero. I.e. if only one of the
-- two expressions fail, it should be non-equal.
-- TODO: Write this using 'curry $ \case {..}'
assertEq
  :: forall m n
   . MonadError SymbolicError m
  => KnownPos n
  => Value m n
  -> Value m n
  -> m (RuntimeValue SymBool)
assertEq (Int lhs) (Int rhs) = pure $ cmpRuntime lhs rhs
assertEq (Int8 lhs) (Int8 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Int16 lhs) (Int16 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Int32 lhs) (Int32 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Int64 lhs) (Int64 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Word lhs) (Word rhs) = pure $ cmpRuntime lhs rhs
assertEq (Word8 lhs) (Word8 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Word16 lhs) (Word16 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Word32 lhs) (Word32 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Word64 lhs) (Word64 rhs) = pure $ cmpRuntime lhs rhs
assertEq (Float lhs) (Float rhs) = pure $ cmpRuntime lhs rhs
assertEq (Double lhs) (Double rhs) = pure $ cmpRuntime lhs rhs
assertEq (ADT lty lhs) (ADT rty rhs) = do
  unless (lty `eqType` rty) $ throwError IllTyped
  (tyCon, tyArgs) <- whyFail IllTyped $ splitTyConApp_maybe lty
  let dataCons = tyConDataCons tyCon

  branches <- forM dataCons $ \dataCon -> do
    -- Ensure that we are in
    let inBranch adt = adtIsDataCon @n adt dataCon
    let eqBranch = cmpRuntime (inBranch lhs) (inBranch rhs)

    -- Gather the field names.
    let names = dataConAccessorNames dataCon
    let tys = scaledThing <$> dataConInstArgTys dataCon tyArgs
    let accessors = zip names tys

    -- Check that every field is the same.
    assertions <- forM accessors $ \(name, ty) -> do
      lfield <- accessField' @m @n lhs name ty
      rfield <- accessField' rhs name ty
      assertEq lfield rfield

    let assertions' = foldl' (liftA2 (.&&)) (pure true) assertions

    pure $ (eqBranch, assertions')

  let invalid = throwError Invalid

  foldM' invalid branches $ \fl (cond, rhs') -> do
    pure $ iteRuntime cond rhs' fl
assertEq (Cast' lco lhs) (Cast' rco rhs) = do
  unless (lco `eqCoercion` rco) $ throwError IllTyped
  assertEq lhs rhs
assertEq _ _ = throwError IllTyped

symbolicBndrs
  :: MonadError SymbolicError m
  => KnownPos n
  => CoreExpr
  -> m [Value m n]
symbolicBndrs expr = do
  let (bndrs, _) = collectBinders expr
  forM bndrs symbolicInstance

symbolicInstance
  :: MonadError SymbolicError m
  => KnownPos n
  => Id
  -> m (Value m n)
symbolicInstance bndr = typedValue symbolic ty
  where
    symbolic :: Solvable c a => RuntimeValue a
    symbolic = pure . sym . fromString $ name
    name = occNameString $ occName bndr
    ty = varType bndr
