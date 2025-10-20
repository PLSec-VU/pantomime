-- TODO: Add more primitives and more operations on them.
-- TODO: Add top-level explanation of why we need this module and how it is
-- implemented under the hood.
{-# LANGUAGE RoleAnnotations #-}

module Pantomime.Primitive.Operation
  ( IntN
  , plusIntN
  , timesIntN
  , absIntN
  , signumIntN
  , negateIntN
  , fromIntegerIntN
  , eqIntN

  , Integer
  , plusInteger
  , timesInteger
  , absInteger
  , signumInteger
  , negateInteger
  , fromIntegerInteger
  ) where

import Prelude qualified as Prelude
import Prelude (Num (..), Eq (..), Bool, ($))

import GHC.TypeNats (Nat, KnownNat)

import Pantomime.Grisette.BitVector qualified as Pantomime

import Grisette.Unified (EvalModeTag(..))

import Data.Coerce (coerce)

-- | Interpretable sized integer primitive.
--
-- Although this has an implementation for usage during runtime, it is expected
-- that this is primarily used to provide interpretations of other data types.
newtype IntN (n :: Nat) where
  IntN :: Pantomime.IntN C n -> IntN n

type role IntN nominal

{-# OPAQUE plusIntN #-}
plusIntN :: forall n. KnownNat n => IntN n -> IntN n -> IntN n
plusIntN = coerce $ (+) @(Pantomime.IntN C n)

{-# OPAQUE timesIntN #-}
timesIntN :: forall n. KnownNat n => IntN n -> IntN n -> IntN n
timesIntN = coerce $ (*) @(Pantomime.IntN C n)

{-# OPAQUE absIntN #-}
absIntN :: forall n. KnownNat n => IntN n -> IntN n
absIntN = coerce $ abs @(Pantomime.IntN C n)

{-# OPAQUE signumIntN #-}
signumIntN :: forall n. KnownNat n => IntN n -> IntN n
signumIntN = coerce $ signum @(Pantomime.IntN C n)

{-# OPAQUE negateIntN #-}
negateIntN :: forall n. KnownNat n => IntN n -> IntN n
negateIntN = coerce $ negate @(Pantomime.IntN C n)

{-# OPAQUE fromIntegerIntN #-}
fromIntegerIntN :: forall n. KnownNat n => Prelude.Integer -> IntN n
fromIntegerIntN = coerce $ fromInteger @(Pantomime.IntN C n)

instance KnownNat n => Num (IntN n) where
  (+) = plusIntN
  (*) = timesIntN
  abs = absIntN
  signum = signumIntN
  negate = negateIntN
  fromInteger = fromIntegerIntN

{-# OPAQUE eqIntN #-}
eqIntN :: IntN n -> IntN n -> Bool
-- FIXME: IntN C is overconstrained for equality sadly: we don't want to
-- require KnownNat. I guess it is best to split C and S off some time. For now,
-- I guess I'll just replace it with an error as we mostly want to interpret
-- this function anyway.
eqIntN = Prelude.undefined

instance Eq (IntN n) where
  (==) = eqIntN

-- newtype WordN (n :: Nat) where
--   WordN :: { unWordN :: Pantomime.WordN C n } -> WordN n

-- | Interpretable unbounded integer primitive.
--
-- Although this has an implementation for usage during runtime, it is expected
-- that this is primarily used to provide interpretations of other data types.
newtype Integer where
  Integer :: Prelude.Integer -> Integer

{-# OPAQUE plusInteger #-}
plusInteger :: Integer -> Integer -> Integer
plusInteger = coerce $ (+) @Prelude.Integer

{-# OPAQUE timesInteger #-}
timesInteger :: Integer -> Integer -> Integer
timesInteger = coerce $ (*) @Prelude.Integer

{-# OPAQUE absInteger #-}
absInteger :: Integer -> Integer
absInteger = coerce $ abs @Prelude.Integer

{-# OPAQUE signumInteger #-}
signumInteger :: Integer -> Integer
signumInteger = coerce $ signum @Prelude.Integer

{-# OPAQUE negateInteger #-}
negateInteger :: Integer -> Integer
negateInteger = coerce $ negate @Prelude.Integer

{-# OPAQUE fromIntegerInteger #-}
fromIntegerInteger :: Prelude.Integer -> Integer
fromIntegerInteger = coerce $ fromInteger @Prelude.Integer

instance Num Integer where
  (+) = plusInteger
  (*) = timesInteger
  abs = absInteger
  signum = signumInteger
  negate = negateInteger
  fromInteger = fromIntegerInteger
