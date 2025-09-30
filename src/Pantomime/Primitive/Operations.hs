-- TODO: Add more primitives and more operations on them.
-- TODO: Add top-level explanation of why we need this module and how it is
-- implemented under the hood.
--
-- Here's one important note already added:
--
-- NOTE: These primitives are explicitly defined as 'data' and not as 'newtype'.
-- This is because we do not want to add their reduction to the 'FamInstEnvs' as
-- this would make fresh variable generation fragile. That is, we really don't
-- want to create casts for these primitives, but the 'FamInstEnvs' does not
-- provide a way to remove these mappings. As such, we instead opt to just not
-- add them in the first place!
-- TODO: We can remove instances from FamInstEnvs by getting the list of
-- elements via 'famInstEnvElts', filtering it and reconstructing the filtered
-- version via 'emptyFamInstEnv' and 'extendFamInstEnvList'.
{-# LANGUAGE RoleAnnotations #-}

module Pantomime.Primitive.Operations
  ( IntN
  , plusIntN
  , timesIntN
  , absIntN
  , signumIntN
  , negateIntN
  , fromIntegerIntN

  , Integer
  , plusInteger
  , timesInteger
  , absInteger
  , signumInteger
  , negateInteger
  , fromIntegerInteger
  ) where

import Prelude qualified as Prelude
import Prelude (Num (..), (.))

import GHC.TypeNats (Nat, KnownNat)

import Pantomime.Grisette.BitVector qualified as Pantomime

import Grisette.Unified (EvalModeTag(..))

import Data.Composition ((.:))
import Data.Function (on)

-- | Interpretable sized integer primitive.
--
-- Although this has an implementation for usage during runtime, it is expected
-- that this is primarily used to provide interpretations of other data types.
--
-- WARNING: Do not change to 'newtype'. Read module comment as to why.
data IntN (n :: Nat) where
  IntN :: { unIntN :: Pantomime.IntN C n } -> IntN n

type role IntN nominal

{-# OPAQUE plusIntN #-}
plusIntN :: KnownNat n => IntN n -> IntN n -> IntN n
plusIntN = IntN .: on (+) unIntN

{-# OPAQUE timesIntN #-}
timesIntN :: KnownNat n => IntN n -> IntN n -> IntN n
timesIntN = IntN .: on (*) unIntN

{-# OPAQUE absIntN #-}
absIntN :: KnownNat n => IntN n -> IntN n
absIntN = IntN . abs . unIntN

{-# OPAQUE signumIntN #-}
signumIntN :: forall n. KnownNat n => IntN n -> IntN n
signumIntN = IntN . signum . unIntN

{-# OPAQUE negateIntN #-}
negateIntN :: KnownNat n => IntN n -> IntN n
negateIntN = IntN . negate . unIntN

{-# OPAQUE fromIntegerIntN #-}
fromIntegerIntN :: KnownNat n => Prelude.Integer -> IntN n
fromIntegerIntN = IntN . fromInteger

instance KnownNat n => Num (IntN n) where
  (+) = plusIntN
  (*) = timesIntN
  abs = absIntN
  signum = signumIntN
  negate = negateIntN
  fromInteger = fromIntegerIntN

-- newtype WordN (n :: Nat) where
--   WordN :: { unWordN :: Pantomime.WordN C n } -> WordN n

-- | Interpretable unbounded integer primitive.
--
-- Although this has an implementation for usage during runtime, it is expected
-- that this is primarily used to provide interpretations of other data types.
--
-- WARNING: Do not change to 'newtype'. Read module comment as to why.
data Integer where
  Integer :: { unInteger :: Prelude.Integer } -> Integer

{-# OPAQUE plusInteger #-}
plusInteger :: Integer -> Integer -> Integer
plusInteger = Integer .: on (+) unInteger

{-# OPAQUE timesInteger #-}
timesInteger :: Integer -> Integer -> Integer
timesInteger = Integer .: on (*) unInteger

{-# OPAQUE absInteger #-}
absInteger :: Integer -> Integer
absInteger = Integer . abs . unInteger

{-# OPAQUE signumInteger #-}
signumInteger :: Integer -> Integer
signumInteger = Integer . signum . unInteger

{-# OPAQUE negateInteger #-}
negateInteger :: Integer -> Integer
negateInteger = Integer . negate . unInteger

{-# OPAQUE fromIntegerInteger #-}
fromIntegerInteger :: Prelude.Integer -> Integer
fromIntegerInteger = Integer . fromInteger

instance Num Integer where
  (+) = plusInteger
  (*) = timesInteger
  abs = absInteger
  signum = signumInteger
  negate = negateInteger
  fromInteger = fromIntegerInteger
