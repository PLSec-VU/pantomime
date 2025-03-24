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

module Symbolic.Runtime
  ( RuntimeValue (..)
  , RuntimeError (..)

  , cmpRuntime
  , iteRuntime
  , assumeRuntime
  ) where

import GHC.Utils.Outputable (Outputable (..), text)
import GHC.Generics (Generic)

import Control.Monad.Except (ExceptT (..), MonadError)

import Data.Functor.Classes (Show1)

import Grisette.Lib.Control.Monad.Except (mrgThrowError)
import Grisette.Unified (EvalModeTag (..), BaseMonad)
import Grisette
  ( Mergeable
  , SimpleMergeable (..)
  , EvalSym
  , SymEq (..)
  , SymBool
  , Default (..)
  , TryMerge
  , Mergeable1
  , SymBranching
  , ToSym (..)
  , ToCon (..)
  , mrgLiftA2, EvalSym1
  )

newtype RuntimeValue mode a where
  RuntimeValue ::
    { unRuntimeValue :: ExceptT RuntimeError (BaseMonad mode) a
    } -> RuntimeValue mode a

deriving via ExceptT RuntimeError (BaseMonad mode)
  instance Monad (BaseMonad mode)
  => Functor (RuntimeValue mode)

deriving via ExceptT RuntimeError (BaseMonad mode)
  instance Monad (BaseMonad mode)
  => Applicative (RuntimeValue mode)

deriving via ExceptT RuntimeError (BaseMonad mode)
  instance Monad (BaseMonad mode)
  => Monad (RuntimeValue mode)

deriving via ExceptT RuntimeError (BaseMonad mode)
  instance TryMerge (BaseMonad mode)
  => TryMerge (RuntimeValue mode)

deriving via ExceptT RuntimeError (BaseMonad mode) a
  instance (Mergeable1 (BaseMonad mode), Mergeable a)
  => Mergeable (RuntimeValue mode a)

deriving via ExceptT RuntimeError (BaseMonad mode) a
  instance (SymBranching (BaseMonad mode), Mergeable a)
  => SimpleMergeable (RuntimeValue mode a)

deriving via ExceptT RuntimeError (BaseMonad mode)
  instance Monad (BaseMonad mode)
  => MonadError RuntimeError (RuntimeValue mode)

deriving via ExceptT RuntimeError (BaseMonad mode) a
  instance (Show1 (BaseMonad mode), Show a)
  => Show (RuntimeValue mode a)

deriving via ExceptT RuntimeError (BaseMonad mode) a
  instance (EvalSym1 (BaseMonad mode), EvalSym a)
  => EvalSym (RuntimeValue mode a)

instance ToSym a b => ToSym (RuntimeValue C a) (RuntimeValue S b) where
  toSym = RuntimeValue . toSym . unRuntimeValue

instance ToSym a b => ToSym (RuntimeValue S a) (RuntimeValue S b) where
  toSym = RuntimeValue . toSym . unRuntimeValue

instance ToCon a b => ToCon (RuntimeValue S a) (RuntimeValue C b) where
  toCon = fmap RuntimeValue . toCon . unRuntimeValue

instance ToCon a b => ToCon (RuntimeValue C a) (RuntimeValue C b) where
  toCon = fmap RuntimeValue . toCon . unRuntimeValue

-- TODO: Add support for all primitive runtime errors.
-- TODO: We could add support for bottom? I guess we would want an option to
-- enable/disable bottom values for the checker then? Technically, we need to
-- deal with errors in any case, so maybe the disable should just ensure the
-- inputs are not bot?
data RuntimeError where
  DivideByZero :: RuntimeError
  -- | Any Symbolic value that cannot be reached in practise.
  --
  -- For example, we create a symbolic BigNatural via SymInteger with a
  -- constraint that the value cannot be negative. This error would be reached
  -- if the constraint solver tries to instantiate a negative number.
  Invalid :: RuntimeError
  deriving Show
  deriving Generic
  deriving Eq
  deriving Mergeable via (Default RuntimeError)
  deriving EvalSym via (Default RuntimeError)
  deriving SymEq via (Default RuntimeError)

instance Outputable RuntimeError where
  ppr = \case
    DivideByZero -> text "divide-by-zero"
    Invalid -> text "invalid"

-- | Compare two runtime values.
--
-- Note that this is different from normal symbolic equivalence in that we do
-- not want to compare error values. An error in a branch should be propagated
-- the root. This function propagates errors in either value and compares them
-- if both are non-error values.
-- TODO: This (and the other runtime functions) should be polymorphic over the
-- evaluation mode.
cmpRuntime
  :: Mergeable a
  => SymEq a
  => RuntimeValue S a
  -> RuntimeValue S a
  -> RuntimeValue S SymBool
cmpRuntime = mrgLiftA2 (.==)

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

-- | Assume that the given condition holds.
-- FIXME: This should respect lazy semantics. The current implementation
-- forces the conditional, which is not what we want from an assert. Assertions
-- should not force evaluation, but just restrict computation given no failure
-- occurred. Maybe the problem is in the comparison function cmpRuntime btw.
-- I'll have to think about it once I add support for bottom values.
assumeRuntime
  :: SimpleMergeable a
  => RuntimeValue S SymBool
  -> RuntimeValue S a
  -> RuntimeValue S a
assumeRuntime cond tr = iteRuntime cond tr $ mrgThrowError Invalid
