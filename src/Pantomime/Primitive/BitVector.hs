{-# LANGUAGE RoleAnnotations #-}

module Pantomime.Primitive.BitVector
  ( BitVector

  -- | Inner KnownNat constraint
  , withNat

  -- | Eq
  , eq

  -- | Ord
  , leZ
  , leS

  -- | Num
  , add
  , mul
  , abs
  , signum
  , negate
  , fromInteger

  -- | Integral
  -- TODO: Add other integral methods!
  , toInteger

  -- | Bits
  , and
  , or
  , xor
  , complement
  , shiftL
  , shiftRL
  , shiftRA
  , rotateL
  , rotateRL
  , rotateRA

  -- | Resize operations.
  , concat
  , extendZ
  , extendS
  , select
  , truncate
  , resizeZ
  , resizeS

  -- | Functions I would rather not have but exist for reasons.
  , stupidSlice
  , stupidMinBound
  ) where

import Prelude qualified
import Prelude
  ( Eq
  , Ord
  , Num
  , Int
  , Integer
  , Applicative (..)
  , Bool (..)
  , ($)
  , (.)
  )

import Data.Bits qualified as Prelude
import Data.Bits (Bits, FiniteBits)

import GHC.TypeLits (OrderingI(..))
import GHC.TypeNats (KnownNat, Nat, type (+), type (<=), type (-))

import Grisette.Unified (EvalModeTag(..))
import Grisette (BitCast(..))

import Control.Monad.Identity (Identity(..))

import Pantomime.Grisette.BitVector (WordN, IntN)
import Pantomime.Grisette.SizedBV (SizedBV (..))
import Pantomime.Dict
  ( SomeNat'(..)
  , Dict (..)
  , cmpNat'
  , geqToLeq
  , typeAdd
  , typeSub
  , unsafeDict
  )

-- TODO: Perhaps it would be good to have both a signed and unsigned version,
-- but then only have one underlying implementation? I.e. perhaps users would
-- find it useful to have a bitvector with default signed behaviour as default
-- for the typeclass implementations.
data BitVector (n :: Nat) where
  BitVector :: KnownNat n => WordN C n -> BitVector n

type role BitVector nominal

unary
  :: (KnownNat n => WordN C n -> WordN C n)
  -> BitVector n
  -> BitVector n
unary f (BitVector x) = BitVector $ f x

binary
  :: (KnownNat n => WordN C n -> WordN C n -> WordN C n)
  -> BitVector n
  -> BitVector n
  -> BitVector n
binary f (BitVector x) (BitVector y) = BitVector $ f x y

cmp
  :: (KnownNat n => WordN C n -> WordN C n -> Bool)
  -> BitVector n
  -> BitVector n
  -> Bool
cmp f (BitVector x) (BitVector y) = f x y

shft
  :: (KnownNat n => WordN C n -> Int -> WordN C n)
  -> BitVector n
  -> Int
  -> BitVector n
shft f (BitVector x) idx = BitVector $ f x idx

{-# OPAQUE withNat #-}
withNat :: forall n a. BitVector n -> (KnownNat n => a) -> a
withNat BitVector {} f = f

{-# OPAQUE eq #-}
eq :: BitVector n -> BitVector n -> Bool
eq = cmp (Prelude.==)

instance Eq (BitVector n) where
  (==) = eq

-- | Unsigned less-than-or-equal.
{-# OPAQUE leZ #-}
leZ :: BitVector n -> BitVector n -> Bool
leZ = cmp (Prelude.<=)

-- | Signed less-than-or-equal.
{-# OPAQUE leS #-}
leS :: forall n. BitVector n -> BitVector n -> Bool
leS (BitVector x) (BitVector y) = bitCast x Prelude.<= bitCast @_ @(IntN C n) y

instance Ord (BitVector n) where
  (<=) = leZ

{-# OPAQUE add #-}
add :: forall n. BitVector n -> BitVector n -> BitVector n
add = binary (Prelude.+)

{-# OPAQUE mul #-}
mul :: forall n. BitVector n -> BitVector n -> BitVector n
mul = binary (Prelude.*)

{-# OPAQUE abs #-}
abs :: forall n. BitVector n -> BitVector n
abs = unary Prelude.abs

{-# OPAQUE signum #-}
signum :: forall n. BitVector n -> BitVector n
signum = unary Prelude.signum

{-# OPAQUE negate #-}
negate :: forall n. BitVector n -> BitVector n
negate = unary Prelude.negate

{-# OPAQUE fromInteger #-}
fromInteger :: forall n. KnownNat n => Integer -> BitVector n
fromInteger = BitVector . Prelude.fromInteger

{-# OPAQUE toInteger #-}
toInteger :: forall n. BitVector n -> Integer
toInteger (BitVector x) = Prelude.toInteger x

instance KnownNat n => Num (BitVector n) where
  (+) = add
  (*) = mul
  abs = abs
  signum = signum
  negate = negate
  fromInteger = fromInteger

{-# OPAQUE and #-}
and :: BitVector n -> BitVector n -> BitVector n
and = binary (Prelude..&.)

{-# OPAQUE or #-}
or :: BitVector n -> BitVector n -> BitVector n
or = binary (Prelude..|.)

{-# OPAQUE xor #-}
xor :: BitVector n -> BitVector n -> BitVector n
xor = binary Prelude.xor

{-# OPAQUE complement #-}
complement :: BitVector n -> BitVector n
complement = unary Prelude.complement

{-# OPAQUE shiftL #-}
shiftL :: BitVector n -> Int -> BitVector n
shiftL = shft Prelude.shiftL

-- | Shift Right Logical rimitive.
{-# OPAQUE shiftRL #-}
shiftRL :: BitVector n -> Int -> BitVector n
shiftRL = shft Prelude.shiftR

-- | Shift Right Arithmetic rimitive.
{-# OPAQUE shiftRA #-}
shiftRA :: forall n. BitVector n -> Int -> BitVector n
shiftRA (BitVector x) idx = do
  let x' = bitCast @_ @(IntN C n) x
  let result = Prelude.shiftR x' idx
  BitVector $ bitCast result

{-# OPAQUE rotateL #-}
rotateL :: BitVector n -> Int -> BitVector n
rotateL = shft Prelude.rotateL

-- | Rotate Right Logical rimitive.
{-# OPAQUE rotateRL #-}
rotateRL :: BitVector n -> Int -> BitVector n
rotateRL = shft Prelude.rotateR

-- | Rotate Right Arithmetic rimitive.
{-# OPAQUE rotateRA #-}
rotateRA :: forall n. BitVector n -> Int -> BitVector n
rotateRA (BitVector x) idx = do
  let x' = bitCast @_ @(IntN C n) x
  let result = Prelude.rotateR x' idx
  BitVector $ bitCast result

instance Bits (BitVector n) where
  (.&.) = and
  (.|.) = or
  xor = xor
  complement = complement
  shiftL = shiftL
  shiftR = shiftRL
  rotateL = rotateL
  rotateR = rotateRL
  bitSize = Prelude.finiteBitSize
  bitSizeMaybe = pure . Prelude.finiteBitSize
  isSigned _ = True

  -- TODO: What should I do with these? Not sure if they require an
  -- interpretation. I'll leave them like this for now, as they're probably not
  -- used within the code we will run.
  testBit = Prelude.undefined
  bit = Prelude.undefined
  popCount = Prelude.undefined

instance FiniteBits (BitVector n) where
  finiteBitSize (BitVector x) = Prelude.finiteBitSize x

{-# OPAQUE concat #-}
concat :: forall l r. BitVector l -> BitVector r -> BitVector (l + r)
concat (BitVector x) (BitVector y) = case typeAdd @l @r of
  SomeNat' -> BitVector $ sizedBVConcat x y

{-# OPAQUE extendZ #-}
extendZ :: forall l r. KnownNat r => l <= r => BitVector l -> BitVector r
extendZ (BitVector x) = BitVector $ sizedBVExtZ x

{-# OPAQUE extendS #-}
extendS :: forall l r. KnownNat r => l <= r => BitVector l -> BitVector r
extendS (BitVector x) = BitVector $ sizedBVExtS x

{-# OPAQUE select #-}
select
  :: forall idx width n
   . KnownNat idx
  => KnownNat width
  => idx + width <= n
  => BitVector n
  -> BitVector width
select (BitVector x) = BitVector $ sizedBVSelect @_ @idx x

truncate
  :: forall width n
   . KnownNat width
  => width <= n
  => BitVector n
  -> BitVector width
truncate = select @0

resizeWith
  :: forall l r
   . KnownNat r
  => (l <= r => BitVector l -> BitVector r)
  -> BitVector l
  -> BitVector r
resizeWith f bv = withNat bv $ case cmpNat' @l @r of
  LTI -> f bv
  EQI -> bv
  GTI -> case geqToLeq @l @r of Dict -> truncate bv

-- TODO: It seems to me that this doesn't need to be opaque as it only uses
-- implemented values. Perhaps the natural comparison of naturals is hard? I
-- guess the KnownNat does need to be concrete anyway, so maybe not. I'll leave
-- it as is for now, maybe we can come back to it! Same for the resizeS btw!
--
-- I guess the alternative would be the inverse, where we implement extend
-- with resize instead.
{-# OPAQUE resizeZ #-}
resizeZ :: forall l r. KnownNat r => BitVector l -> BitVector r
resizeZ = resizeWith extendZ

{-# OPAQUE resizeS #-}
resizeS :: forall l r. KnownNat r => BitVector l -> BitVector r
resizeS = resizeWith extendS

-- TODO: We only have this function because we don't have support for natural
-- number arithmetic yet. Hence, we cannot implement the slice by calculating on
-- the KnownNat... For now, we just have a built-in implementation for it. Once
-- we support calculations on Nat, we can evict this :)
{-# OPAQUE stupidSlice #-}
stupidSlice
  :: forall upper top idx
   . KnownNat upper
  => KnownNat idx
  => BitVector (upper + 1 + top)
  -> BitVector (upper + 1 - idx)
stupidSlice x = runIdentity do
  Dict <- pure $ withNat x (Dict @(KnownNat (upper + 1 + top)))
  SomeNat' @upper1 <- pure $ typeAdd @upper @1
  SomeNat' @width <- pure $ typeSub @upper1 @idx

  -- Is this actually true?
  Dict <- pure $ unsafeDict @(idx + width <= upper + 1 + top)

  pure $ select @idx @width @(upper + 1 + top) x

-- TODO: We only have this function because Clash has incredibly silly
-- constraints on their functions. 'minBound#' doesn't have a KnownNat
-- requirement because BitVector is implemented in a stupid way that tracks a
-- mask instead of its size. For now, we just create a function that captures
-- the behaviour by doing type-level machinery under the hood. Really though,
-- I just want to express my annoyance with Clash as there is no great way to
-- resolve this issue... (unlike stupidSlice, which is not actually that stupid)
--
-- There isn't even a real implementation for this thing btw. (and no, we're not
-- going to adopt the clash way of encoding this thing!)
{-# OPAQUE stupidMinBound #-}
stupidMinBound :: BitVector n
stupidMinBound = Prelude.undefined
