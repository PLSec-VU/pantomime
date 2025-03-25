{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Symbolic.MonadEval
  ( MonadEval
  , EvalError (..)

  , SymbolicState (..)
  , freshIdx

  , EvalEq (..)
  , EvalIte (..)
  , EvalAssume (..)
  ) where

import GHC.Plugins
import GHC.MonadCore

import Grisette (SymBool, SimpleMergeable (..), mrgLiftA2, SymEq (..), Mergeable)
import Grisette.Unified (GetBool, EvalModeTag (..))

import Control.Monad.Except (MonadError)
import Control.Monad.State (MonadState (..))

import Symbolic.Runtime
import Data.Composition ((.:), (.:.))
import Grisette.Lib.Control.Monad.Except (mrgThrowError)

-- TODO: Remove MonadCore from the requirements.
type MonadEval m = (MonadError EvalError m, MonadState SymbolicState m, MonadCore m)

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

-- | A typeclass for operations that are symbolically checked for equivalence.
--
-- The main purpose is to allow for error propagation when performing common
-- operations on data types containing runtime values. As this is an ideom
-- that requires a lot of wrapping/unwrapping from these data types, we instead
-- capture it in this way.
class MonadEval m => EvalEq m a where
  evalEq
    :: a
    -> a
    -> m (RuntimeValue S (GetBool S))

instance (MonadEval m, Mergeable a, SymEq a) => EvalEq m (RuntimeValue S a) where
  evalEq = pure .: mrgLiftA2 (.==)

-- | A typeclass for operations that are symbolically branched.
--
-- The main purpose is to allow for error propagation when performing common
-- operations on data types containing runtime values. As this is an ideom
-- that requires a lot of wrapping/unwrapping from these data types, we instead
-- capture it in this way.
class MonadEval m => EvalIte m a where
  evalIte
    :: RuntimeValue S (GetBool S)
    -> a
    -> a
    -> m a

instance (MonadEval m, SimpleMergeable a) => EvalIte m (RuntimeValue S a) where
  evalIte = pure .:. iteRuntime

-- | A typeclass for operations that allow for symbolic assumptions.
class EvalAssume a where
  -- TODO: Unsure if this should support lazy semantics actually?
  evalAssume
    :: RuntimeValue S (GetBool S)
    -> a
    -> a

-- FIXME: This should respect lazy semantics. The current implementation
-- forces the conditional, which is not what we want from an assumption no?
-- Assumptions should not force evaluation, but just restrict computation
-- given no failure occurred. Maybe the problem is in the comparison function
-- cmpRuntime btw. I'll have to think about it once I add support for bottom
-- values.
instance SimpleMergeable a => EvalAssume (RuntimeValue S a) where
  evalAssume cond tr = iteRuntime cond tr $ mrgThrowError Invalid

-- | Branch over a runtime symbolic boolean.
--
-- If the conditional of an if statement can fail, we first wish to check this
-- before proceeding to choose either branch. This function captures that idea.
iteRuntime
  :: SimpleMergeable a
  => RuntimeValue S SymBool
  -> RuntimeValue S a
  -> RuntimeValue S a
  -> RuntimeValue S a
iteRuntime cond tr fl = do
  cond' <- cond
  mrgIte cond' tr fl
