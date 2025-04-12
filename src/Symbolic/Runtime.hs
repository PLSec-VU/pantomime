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
{-# LANGUAGE QuantifiedConstraints #-}

module Symbolic.Runtime
  ( RuntimeValue (..)
  , unRuntimeC
  , unRuntimeS
  , RuntimeError (..)
  ) where

import GHC.Utils.Outputable (Outputable (..), text)
import GHC.Generics (Generic)

import Control.Monad.Except (ExceptT (..), MonadError, runExceptT)
import Control.Monad.Identity (runIdentity)

import Data.Functor.Classes (Show1, Eq1)

import Grisette.Unified (EvalModeTag (..), BaseMonad)
import Grisette
  ( Mergeable
  , Mergeable1
  , SimpleMergeable
  , TryMerge
  , EvalSym
  , EvalSym1
  , SymEq
  , SymEq1
  , SymBranching
  , ToSym (..)
  , ToCon (..)
  , Default (..)
  , PPrint
  , Union
  )

newtype RuntimeValue mode a where
  RuntimeValue ::
    { unRuntimeValue :: ExceptT RuntimeError (BaseMonad mode) a
    } -> RuntimeValue mode a

unRuntimeC :: RuntimeValue C a -> Either RuntimeError a
unRuntimeC = runIdentity . runExceptT . unRuntimeValue

unRuntimeS :: RuntimeValue S a -> Union (Either RuntimeError a)
unRuntimeS = runExceptT . unRuntimeValue

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

deriving via ExceptT RuntimeError (BaseMonad mode)
  instance (Mergeable1 (BaseMonad mode))
  => Mergeable1 (RuntimeValue mode)

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
  instance (Eq1 (BaseMonad mode), Eq a)
  => Eq (RuntimeValue mode a)

deriving via ExceptT RuntimeError (BaseMonad mode) a
  instance (EvalSym1 (BaseMonad mode), EvalSym a)
  => EvalSym (RuntimeValue mode a)

deriving via ExceptT RuntimeError (BaseMonad mode) a
  instance (SymEq1 (BaseMonad mode), SymEq a)
  => SymEq (RuntimeValue mode a)

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
  Overflow :: RuntimeError
  Underflow :: RuntimeError
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
  deriving Mergeable via Default RuntimeError
  deriving EvalSym via Default RuntimeError
  deriving SymEq via Default RuntimeError
  deriving PPrint via Default RuntimeError

instance Outputable RuntimeError where
  ppr = \case
    Overflow -> text "overflow"
    Underflow -> text "underflow"
    DivideByZero -> text "divide-by-zero"
    Invalid -> text "invalid"
