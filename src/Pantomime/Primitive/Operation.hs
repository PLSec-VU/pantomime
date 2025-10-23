-- TODO: Add more primitives and more operations on them.
-- TODO: Add top-level explanation of why we need this module and how it is
-- implemented under the hood.
{-# LANGUAGE RoleAnnotations #-}

module Pantomime.Primitive.Operation
  ( Num (..)
  , Bits (..)
  , Eq (..)
  , Ord (..)
  , SizedBV (..)

  , IntN
  , eqIntN
  , leIntN
  , plusIntN
  , timesIntN
  , absIntN
  , signumIntN
  , negateIntN
  , fromIntegerIntN
  , andIntN
  , orIntN
  , xorIntN
  , complementIntN
  , shiftLIntN
  , shiftRIntN
  , rotateLIntN
  , rotateRIntN
  , sizedBVConcatIntN
  , sizedBVExtZIntN
  , sizedBVExtSIntN
  , sizedBVExtIntN
  , sizedBVSelectIntN

  , Integer
  , plusInteger
  , timesInteger
  , absInteger
  , signumInteger
  , negateInteger
  , fromIntegerInteger
  ) where

import Prelude qualified as Prelude
import Prelude
  ( Num (..)
  , Eq (..)
  , Ord (..)
  , Applicative (..)
  , Bool (..)
  , ($)
  , (.)
  )

import GHC.TypeNats (type (+), type (<=), Nat, KnownNat)

import Pantomime.Grisette.BitVector qualified as Pantomime
import Pantomime.Grisette.SizedBV (SizedBV (..))

import Grisette.Unified (EvalModeTag(..))

import Data.Bits (Bits (..), FiniteBits (..))
import Data.Coerce (coerce)

-- | Interpretable sized integer primitive.
--
-- Although this has an implementation for usage during runtime, it is expected
-- that this is primarily used to provide interpretations of other data types.
newtype IntN (n :: Nat) where
  IntN :: Pantomime.IntN C n -> IntN n

type role IntN nominal

{-# OPAQUE eqIntN #-}
eqIntN :: IntN n -> IntN n -> Bool
-- FIXME: IntN C is overconstrained for equality sadly: we don't want to
-- require KnownNat. I guess it is best to split C and S off some time. For now,
-- I guess I'll just replace it with an error as we mostly want to interpret
-- this function anyway.
eqIntN = Prelude.undefined

instance Eq (IntN n) where
  (==) = eqIntN

{-# OPAQUE leIntN #-}
leIntN :: forall n. KnownNat n => IntN n -> IntN n -> Bool
leIntN = coerce $ (<=) @(Pantomime.IntN C n)

instance KnownNat n => Ord (IntN n) where
  (<=) = leIntN

{-# OPAQUE plusIntN #-}
plusIntN :: forall n. KnownNat n => IntN n -> IntN n -> IntN n
plusIntN = coerce $ (+) @(Pantomime.IntN C _)

{-# OPAQUE timesIntN #-}
timesIntN :: forall n. KnownNat n => IntN n -> IntN n -> IntN n
timesIntN = coerce $ (*) @(Pantomime.IntN C _)

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

{-# OPAQUE andIntN #-}
andIntN :: forall n. KnownNat n => IntN n -> IntN n -> IntN n
andIntN = coerce $ (.&.) @(Pantomime.IntN C n)

{-# OPAQUE orIntN #-}
orIntN :: forall n. KnownNat n => IntN n -> IntN n -> IntN n
orIntN = coerce $ (.|.) @(Pantomime.IntN C n)

{-# OPAQUE xorIntN #-}
xorIntN :: forall n. KnownNat n => IntN n -> IntN n -> IntN n
xorIntN = coerce $ xor @(Pantomime.IntN C n)

{-# OPAQUE complementIntN #-}
complementIntN :: forall n. KnownNat n => IntN n -> IntN n
complementIntN = coerce $ complement @(Pantomime.IntN C n)

{-# OPAQUE shiftLIntN #-}
shiftLIntN :: forall n. KnownNat n => IntN n -> Prelude.Int -> IntN n
shiftLIntN = coerce $ shiftL @(Pantomime.IntN C n)

{-# OPAQUE shiftRIntN #-}
shiftRIntN :: forall n. KnownNat n => IntN n -> Prelude.Int -> IntN n
shiftRIntN = coerce $ shiftR @(Pantomime.IntN C n)

{-# OPAQUE rotateLIntN #-}
rotateLIntN :: forall n. KnownNat n => IntN n -> Prelude.Int -> IntN n
rotateLIntN = coerce $ rotateL @(Pantomime.IntN C n)

{-# OPAQUE rotateRIntN #-}
rotateRIntN :: forall n. KnownNat n => IntN n -> Prelude.Int -> IntN n
rotateRIntN = coerce $ rotateR @(Pantomime.IntN C n)

instance KnownNat n => Bits (IntN n) where
  (.&.) = andIntN
  (.|.) = orIntN
  xor = xorIntN
  complement = complementIntN
  shiftL = shiftLIntN
  shiftR = shiftRIntN
  rotateL = rotateLIntN
  rotateR = rotateRIntN

  -- These don't require an interpretation, so we leave them as is.
  bitSize = finiteBitSize
  bitSizeMaybe = pure . finiteBitSize
  isSigned _ = True

  -- TODO: What should I do with these? Not sure if they require an
  -- interpretation. I'll leave them like this for now, as they're probably not
  -- used within the code we will run.
  testBit = Prelude.undefined
  bit = Prelude.undefined
  popCount = Prelude.undefined

instance KnownNat n => FiniteBits (IntN n) where
  finiteBitSize = coerce $ finiteBitSize @(Pantomime.IntN C n)

{-# OPAQUE sizedBVConcatIntN #-}
sizedBVConcatIntN
  :: forall l r
   . KnownNat l
  => KnownNat r
  => IntN l
  -> IntN r
  -> IntN (l + r)
sizedBVConcatIntN = coerce $ sizedBVConcat @(Pantomime.IntN C)

{-# OPAQUE sizedBVExtZIntN #-}
sizedBVExtZIntN
  :: forall l r
   . KnownNat l
  => KnownNat r
  => l <= r
  => IntN l
  -> IntN r
sizedBVExtZIntN = coerce $ sizedBVExtZ @(Pantomime.IntN C)

{-# OPAQUE sizedBVExtSIntN #-}
sizedBVExtSIntN
  :: forall l r
   . KnownNat l
  => KnownNat r
  => l <= r
  => IntN l
  -> IntN r
sizedBVExtSIntN = coerce $ sizedBVExtS @(Pantomime.IntN C)

{-# OPAQUE sizedBVExtIntN #-}
sizedBVExtIntN
  :: forall l r
   . KnownNat l
  => KnownNat r
  => l <= r
  => IntN l
  -> IntN r
sizedBVExtIntN = coerce $ sizedBVExt @(Pantomime.IntN C)

{-# OPAQUE sizedBVSelectIntN #-}
sizedBVSelectIntN
  :: forall idx width n
   . KnownNat idx
  => KnownNat width
  => KnownNat n
  => idx + width <= n
  => IntN n
  -> IntN width
sizedBVSelectIntN = coerce $ sizedBVSelect @(Pantomime.IntN C) @idx

instance SizedBV IntN where
  sizedBVConcat = sizedBVConcatIntN
  sizedBVExtZ = sizedBVExtZIntN
  sizedBVExtS = sizedBVExtSIntN
  sizedBVExt = sizedBVExtIntN
  sizedBVSelect @idx = sizedBVSelectIntN @idx

-- TODO:
-- Implement the following typeclasses for IntN:
-- - Real
-- - Enum
-- - Integral
-- - Bits
--
-- Should I implement some direct conversion functions for e.g. IntN to WordN?
-- My intuition says that going through Integer should yield the same result, so
-- I don't see the point.

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
