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
{-# LANGUAGE QuantifiedConstraints #-}

module Pantomime.Runtime
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

import Grisette.Unified (EvalModeTag (..), DecideEvalMode (..))
import Grisette
  ( Mergeable (..)
  , Mergeable1 (..)
  , SimpleMergeable (..)
  , SimpleMergeable1 (..)
  , TryMerge (..)
  , EvalSym
  , EvalSym1
  , SymEq
  , SymEq1
  , SymBranching
  , GenSym (..)
  , GenSymSimple (..)
  , ToSym (..)
  , ToCon (..)
  , Default (..)
  , PPrint
  , derivedNoSpecFresh
  , chooseUnionFresh
  )

import Pantomime.Grisette.Union

newtype RuntimeValue mode a where
  RuntimeValue ::
    { unRuntimeValue :: ExceptT RuntimeError (Union mode) a
    } -> RuntimeValue mode a

unRuntimeC :: RuntimeValue C a -> Either RuntimeError a
unRuntimeC = runIdentity . unUnion . runExceptT . unRuntimeValue

unRuntimeS :: RuntimeValue S a -> Union S (Either RuntimeError a)
unRuntimeS = runExceptT . unRuntimeValue

deriving via ExceptT RuntimeError (Union mode)
  instance DecideEvalMode mode
  => Functor (RuntimeValue mode)

deriving via ExceptT RuntimeError (Union mode)
  instance DecideEvalMode mode
  => Applicative (RuntimeValue mode)

deriving via ExceptT RuntimeError (Union mode)
  instance DecideEvalMode mode
  => Monad (RuntimeValue mode)

deriving via ExceptT RuntimeError (Union mode)
  instance DecideEvalMode mode
  => TryMerge (RuntimeValue mode)

deriving via ExceptT RuntimeError (Union mode) a
  instance (DecideEvalMode mode, Mergeable a)
  => Mergeable (RuntimeValue mode a)

deriving via ExceptT RuntimeError (Union mode)
  instance DecideEvalMode mode
  => Mergeable1 (RuntimeValue mode)

deriving via ExceptT RuntimeError (Union S) a
  instance Mergeable a
  => SimpleMergeable (RuntimeValue S a)

deriving via ExceptT RuntimeError (Union S)
  instance SimpleMergeable1 (RuntimeValue S)

deriving via ExceptT RuntimeError (Union S)
  instance SymBranching (RuntimeValue S)

deriving via ExceptT RuntimeError (Union mode)
  instance DecideEvalMode mode
  => MonadError RuntimeError (RuntimeValue mode)

deriving via ExceptT RuntimeError (Union mode) a
  instance (DecideEvalMode mode, Show a)
  => Show (RuntimeValue mode a)

deriving via ExceptT RuntimeError (Union mode)
  instance DecideEvalMode mode
  => Show1 (RuntimeValue mode)

deriving via ExceptT RuntimeError (Union mode) a
  instance (DecideEvalMode mode, Eq a)
  => Eq (RuntimeValue mode a)

deriving via ExceptT RuntimeError (Union mode)
  instance DecideEvalMode mode
  => Eq1 (RuntimeValue mode)

deriving via ExceptT RuntimeError (Union mode) a
  instance (DecideEvalMode mode, EvalSym a)
  => EvalSym (RuntimeValue mode a)

deriving via ExceptT RuntimeError (Union mode)
  instance DecideEvalMode mode
  => EvalSym1 (RuntimeValue mode)

deriving via ExceptT RuntimeError (Union mode) a
  instance (DecideEvalMode mode, SymEq a)
  => SymEq (RuntimeValue mode a)

deriving via ExceptT RuntimeError (Union mode)
  instance DecideEvalMode mode
  => SymEq1 (RuntimeValue mode)

instance (DecideEvalMode mode, ToSym a b) => ToSym (RuntimeValue mode a) (RuntimeValue S b) where
  toSym = RuntimeValue . toSym . unRuntimeValue

instance (DecideEvalMode mode, ToCon a b) => ToCon (RuntimeValue S a) (RuntimeValue mode b) where
  toCon = fmap RuntimeValue . toCon . unRuntimeValue

instance (GenSym () RuntimeError, GenSym () a) => GenSym () (RuntimeValue S a)

instance (GenSym espec RuntimeError, GenSym aspec a) => GenSym (Either espec aspec) (RuntimeValue S a)

instance (GenSym espec RuntimeError, GenSym aspec a) => GenSym (espec, aspec) (RuntimeValue S a)

instance (GenSym () RuntimeError, GenSym () a) => GenSymSimple () (RuntimeValue S a) where
  simpleFresh _ = simpleFresh ((), ())

instance (GenSym espec RuntimeError, GenSym aspec a) => GenSymSimple (Either espec aspec) (RuntimeValue S a) where
  simpleFresh = \case
    Left espec -> wrap . fmap Left <$> fresh espec
    Right aspec -> wrap . fmap Right <$> fresh aspec
    where
      wrap = RuntimeValue . ExceptT . Union

instance (GenSym espec RuntimeError, GenSym aspec a) => GenSymSimple (espec, aspec) (RuntimeValue S a) where
  simpleFresh (espec, aspec) = do
    res <- fresh aspec
    err <- fresh espec
    let wrap = RuntimeValue . ExceptT . Union
    wrap <$> chooseUnionFresh [Left <$> err, Right <$> res]

-- TODO: Add support for all primitive runtime errors.
-- TODO: We could add support for bottom? I guess we would want an option to
-- enable/disable bottom values for the checker then? Technically, we need to
-- deal with errors in any case, so maybe the disable should just ensure the
-- inputs are not bot? How is bottom different from these other errors? Perhaps
-- we don't need to special case it. When creating fresh values, we should have
-- some flag to specify whether the fresh values should be considered fallible.
data RuntimeError where
  Overflow :: RuntimeError
  Underflow :: RuntimeError
  DivideByZero :: RuntimeError

  -- | Any Symbolic value that cannot be reached in practise.
  --
  -- For example, we create a DataCon via a word sized integer. The integer
  -- should always be a valid DataCon. This error would be reached if the
  -- constraint solver tries to instantiate an invalid DataCon.
  Invalid :: RuntimeError
  deriving Show
  deriving Generic
  deriving Eq
  deriving Mergeable via Default RuntimeError
  deriving EvalSym via Default RuntimeError
  deriving SymEq via Default RuntimeError
  deriving PPrint via Default RuntimeError

instance GenSym RuntimeError RuntimeError where

instance GenSym () RuntimeError where
  fresh = derivedNoSpecFresh

instance GenSymSimple RuntimeError RuntimeError where
  simpleFresh = pure

instance Outputable RuntimeError where
  ppr = \case
    Overflow -> text "overflow"
    Underflow -> text "underflow"
    DivideByZero -> text "divide-by-zero"
    Invalid -> text "invalid"
