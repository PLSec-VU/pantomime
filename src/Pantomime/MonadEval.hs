{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Pantomime.MonadEval
  ( MonadEval
  , EvalError (..)

  , Constraints
  , Forceable (..)
  , Spineable (..)

  , EvalIte (..)
  , WeakEq (..)
  ) where

import GHC.Plugins

import Grisette.Unified (EvalModeTag (..), DecideEvalMode (..))
import Grisette 
  ( SymBool
  , LogicalOp (..)
  , SymEq (..)
  , Mergeable
  , SimpleMergeable (..)
  , MonadFresh
  , simpleMerge
  )

import Control.Monad (void)
import Control.Monad.Except (MonadError)

import Data.Composition ((.:.))

import Pantomime.Monad.GHC
import Pantomime.Runtime

-- TODO: Remove MonadCore from the requirements.
type MonadEval m =
  ( MonadError EvalError m
  , MonadFresh m
  , MonadCore m
  , HasModGuts m
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

type Constraints mode = RuntimeValue mode ()

-- | Forceable values, which can take any constraints produced when a value is
-- forced.
class Forceable mode a where
  -- | Force the spine of the given argument, passing any constraints onto
  -- itself.
  force :: Constraints mode -> a -> a

instance DecideEvalMode mode => Forceable mode (RuntimeValue mode a) where
  force s v = s >> v

-- | Any value with a spine whose error constraints can be extracted.
class Spineable mode a where
  -- | Gather the error constraints from the spine of the expression.
  spine :: a -> Constraints mode

instance DecideEvalMode mode => Spineable mode (RuntimeValue mode a) where
  spine = void

class MonadEval m => EvalIte m a where
  evalIte :: SymBool -> a -> a -> m a

instance (MonadEval m, Mergeable a) => EvalIte m (RuntimeValue S a) where
  evalIte = pure .:. mrgIte

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

    let lhs' = unRuntimeS lhs
    let rhs' = unRuntimeS rhs
    let result = liftA2 cmp lhs' rhs'

    pure $ simpleMerge result
