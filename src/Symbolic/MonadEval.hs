{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Symbolic.MonadEval
  ( MonadEval
  , EvalError (..)

  , SymbolicState (..)
  , freshIdx

  , StrictIte (..)
  , WeakEq (..)
  ) where

import GHC.Plugins
import GHC.MonadCore

import Grisette.Unified (GetBool, EvalModeTag (..))
import Grisette 
  ( SymBool
  , LogicalOp (..)
  , SymEq (..)
  , Mergeable
  , SimpleMergeable (..)
  , simpleMerge
  )

import Control.Monad.Except (MonadError, runExceptT)
import Control.Monad.State (MonadState (..))

import Types (HasModGuts')

import Symbolic.Runtime

-- TODO: Remove MonadCore from the requirements.
type MonadEval m =
  ( MonadError EvalError m
  , MonadState SymbolicState m
  , MonadCore m
  , HasModGuts' m
  )

-- TODO: These errors give very little information on what went actually wrong.
-- I should allow some information to be tagged onto them...
data EvalError where
  IllTyped :: EvalError
  UnsupportedExpr :: EvalError
  UnboundVariable :: EvalError
  deriving Show

instance Outputable EvalError where
  ppr = \case
    IllTyped -> text "ill-typed"
    UnsupportedExpr -> text "unsupported expression"
    UnboundVariable -> text "unbound variable"

-- | State to track the next unique index for a symbolic identifier.
newtype SymbolicState where
  SymbolicState :: { nextIdx :: Int } -> SymbolicState

freshIdx :: MonadState SymbolicState m => m Int
freshIdx = state $ \s -> do
    let idx = nextIdx s
    let s' = s { nextIdx = idx + 1 }
    (idx, s')

class MonadEval m => StrictIte m a where
  strictIte :: RuntimeValue S (GetBool S) -> a -> a -> m a

instance (MonadEval m, Mergeable a) => StrictIte m (RuntimeValue S a) where
  strictIte cond tr fl = pure $ do
    cond' <- cond
    mrgIte cond' tr fl

-- TODO: We don't distinguish between weak and strong equivalence anymore.
-- We should perhaps change the name?
class MonadEval m => WeakEq m a where
  weakEq :: a -> a -> m SymBool

instance (MonadEval m, SymEq a) => WeakEq m (RuntimeValue S a) where
  weakEq lhs rhs = do
    let cmp = curry $ \case
          (Left Invalid, _) -> true
          (_, Left Invalid) -> true
          (lhs', rhs') -> lhs' .== rhs'

    let unwrap = runExceptT . unRuntimeValue

    let lhs' = unwrap lhs
    let rhs' = unwrap rhs
    let result = liftA2 cmp lhs' rhs'

    pure $ simpleMerge result
