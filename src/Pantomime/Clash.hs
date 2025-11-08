-- TODO: This file should not be part of pantomime, but should go into a
-- separate package.
-- TODO: We should allow types to be interpreted also if they require strictly
-- less typeclass constraints.
-- TODO: We should allow subtyping for constraints, such that we don't need this
-- no warning pragma anymore!
{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PolyKinds #-}

module Pantomime.Clash
  ( axioms
  ) where

import Pantomime.Axiom (PluginAxioms (..))
-- import Pantomime.Primitive.Operation hiding (Integer)
import Pantomime.Primitive.BitVector qualified as Pantomime
import Pantomime.Dict (Dict (..), unsafeDict)

import Clash.Promoted.Nat (SNat (..))

import Clash.Sized.Internal.BitVector (Bit)
import Clash.Sized.Internal.BitVector qualified as Bit
  ( eq##
  , neq##
  , msb#
  , high
  , low
  )
import Clash.Sized.Internal.BitVector (BitVector)
import Clash.Sized.Internal.BitVector qualified as BitVector
import Clash.Sized.Internal.Unsigned (Unsigned)
import Clash.Sized.Internal.Unsigned qualified as Unsigned
import Clash.Sized.Internal.Signed (Signed)
import Clash.Sized.Internal.Signed qualified as Signed

import Data.Bits (Bits (..), FiniteBits (..))

import GHC.Base (Coercible, coerce)
import GHC.TypeNats (type (+), type (-), type (<=), KnownNat)
import GHC.Exts (IsList (..))
import GHC.Num (Natural)

plusSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Signed n
  -> Signed n
  -> Signed n
plusSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (+) @(Pantomime.BitVector n)

subSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Signed n
  -> Signed n
  -> Signed n
subSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (-) @(Pantomime.BitVector n)

mulSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Signed n
  -> Signed n
  -> Signed n
mulSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (*) @(Pantomime.BitVector n)

negateSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Signed n
  -> Signed n
negateSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n
    go = coerce $ negate @(Pantomime.BitVector n)

complementSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Signed n
  -> Signed n
complementSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n
    go = coerce $ complement @(Pantomime.BitVector n)

andSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Signed n
  -> Signed n
  -> Signed n
andSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (.&.) @(Pantomime.BitVector n)

orSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Signed n
  -> Signed n
  -> Signed n
orSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (.|.) @(Pantomime.BitVector n)

xorSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Signed n
  -> Signed n
  -> Signed n
xorSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ xor @(Pantomime.BitVector n)

absSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Signed n
  -> Signed n
absSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n
    go = coerce $ abs @(Pantomime.BitVector n)

eqSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => Signed n
  -> Signed n
  -> Bool
eqSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (==) @(Pantomime.BitVector n)

neqSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => Signed n
  -> Signed n
  -> Bool
neqSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (/=) @(Pantomime.BitVector n)

ltSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => Signed n
  -> Signed n
  -> Bool
ltSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (<) @(Pantomime.BitVector n)

leSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => Signed n
  -> Signed n
  -> Bool
leSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce Pantomime.leS

gtSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => Signed n
  -> Signed n
  -> Bool
gtSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (>) @(Pantomime.BitVector n)

geSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => Signed n
  -> Signed n
  -> Bool
geSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (>=) @(Pantomime.BitVector n)

shiftLSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Signed n
  -> Int
  -> Signed n
shiftLSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> Int -> bv n
    go = coerce $ shiftL @(Pantomime.BitVector n)

shiftRSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Signed n
  -> Int
  -> Signed n
shiftRSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> Int -> bv n
    go = coerce $ shiftR @(Pantomime.BitVector n)

fromIntegerSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Integer
  -> Signed n
fromIntegerSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => Integer -> bv n
    go = coerce $ fromInteger @(Pantomime.BitVector n)

sizeSigned
  :: forall n
   . Coercible Signed Pantomime.BitVector
  => KnownNat n
  => Signed n
  -> Int
sizeSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> Int
    go = coerce $ finiteBitSize @(Pantomime.BitVector n)

unpackSigned
  :: forall n
   . KnownNat n
  => Coercible BitVector Pantomime.BitVector
  => Coercible Signed Pantomime.BitVector
  => BitVector n
  -> Signed n
unpackSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => Coercible bv' Pantomime.BitVector => bv' n -> bv n
    go = coerce

packSigned
  :: forall n
   . KnownNat n
  => Coercible Signed Pantomime.BitVector
  => Coercible BitVector Pantomime.BitVector
  => Signed n
  -> BitVector n
packSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => Coercible bv' Pantomime.BitVector => bv n -> bv' n
    go = coerce

resizeSigned
  :: forall r l
   . Coercible Signed Pantomime.BitVector
  => KnownNat l
  => KnownNat r
  => Signed l
  -> Signed r
resizeSigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv l -> bv r
    go = coerce Pantomime.resizeS

plusUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => KnownNat n
  => Unsigned n
  -> Unsigned n
  -> Unsigned n
plusUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (+) @(Pantomime.BitVector n)

subUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => KnownNat n
  => Unsigned n
  -> Unsigned n
  -> Unsigned n
subUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (-) @(Pantomime.BitVector n)

mulUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => KnownNat n
  => Unsigned n
  -> Unsigned n
  -> Unsigned n
mulUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (*) @(Pantomime.BitVector n)

negateUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => KnownNat n
  => Unsigned n
  -> Unsigned n
negateUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n
    go = coerce $ negate @(Pantomime.BitVector n)

complementUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => KnownNat n
  => Unsigned n
  -> Unsigned n
complementUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n
    go = coerce $ complement @(Pantomime.BitVector n)

andUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => Unsigned n
  -> Unsigned n
  -> Unsigned n
andUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (.&.) @(Pantomime.BitVector n)

orUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => Unsigned n
  -> Unsigned n
  -> Unsigned n
orUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (.|.) @(Pantomime.BitVector n)

xorUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => Unsigned n
  -> Unsigned n
  -> Unsigned n
xorUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ xor @(Pantomime.BitVector n)

eqUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => Unsigned n
  -> Unsigned n
  -> Bool
eqUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (==) @(Pantomime.BitVector n)

neqUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => Unsigned n
  -> Unsigned n
  -> Bool
neqUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (/=) @(Pantomime.BitVector n)

ltUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => Unsigned n
  -> Unsigned n
  -> Bool
ltUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (<) @(Pantomime.BitVector n)

leUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => Unsigned n
  -> Unsigned n
  -> Bool
leUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (<=) @(Pantomime.BitVector n)

gtUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => Unsigned n
  -> Unsigned n
  -> Bool
gtUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (>) @(Pantomime.BitVector n)

geUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => Unsigned n
  -> Unsigned n
  -> Bool
geUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (>=) @(Pantomime.BitVector n)

shiftLUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => KnownNat n
  => Unsigned n
  -> Int
  -> Unsigned n
shiftLUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> Int -> bv n
    go = coerce $ shiftL @(Pantomime.BitVector n)

shiftRUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => KnownNat n
  => Unsigned n
  -> Int
  -> Unsigned n
shiftRUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> Int -> bv n
    go = coerce $ shiftR @(Pantomime.BitVector n)

fromIntegerUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => KnownNat n
  => Integer
  -> Unsigned n
fromIntegerUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => Integer -> bv n
    go = coerce $ fromInteger @(Pantomime.BitVector n)

sizeUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => KnownNat n
  => Unsigned n
  -> Int
sizeUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> Int
    go = coerce $ finiteBitSize @(Pantomime.BitVector n)

resizeUnsigned
  :: forall l r
   . Coercible Unsigned Pantomime.BitVector
  => KnownNat r
  => Unsigned l
  -> Unsigned r
resizeUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => bv l -> bv r
    go = coerce Pantomime.resizeZ

unpackUnsigned
  :: forall n
   . KnownNat n
  => Coercible BitVector Pantomime.BitVector
  => Coercible Unsigned Pantomime.BitVector
  => BitVector n
  -> Unsigned n
unpackUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => Coercible bv' Pantomime.BitVector => bv' n -> bv n
    go = coerce

packUnsigned
  :: forall n
   . Coercible Unsigned Pantomime.BitVector
  => Coercible BitVector Pantomime.BitVector
  => Unsigned n
  -> BitVector n
packUnsigned = go
  where
    go :: Coercible bv Pantomime.BitVector => Coercible bv' Pantomime.BitVector => bv n -> bv' n
    go = coerce

plusBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
  -> BitVector n
plusBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (+) @(Pantomime.BitVector n)

subBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
  -> BitVector n
subBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (-) @(Pantomime.BitVector n)

mulBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
  -> BitVector n
mulBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (*) @(Pantomime.BitVector n)

negateBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
negateBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n
    go = coerce $ negate @(Pantomime.BitVector n)

complementBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
complementBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n
    go = coerce $ complement @(Pantomime.BitVector n)

andBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
  -> BitVector n
andBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (.&.) @(Pantomime.BitVector n)

orBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
  -> BitVector n
orBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ (.|.) @(Pantomime.BitVector n)

xorBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
  -> BitVector n
xorBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> bv n
    go = coerce $ xor @(Pantomime.BitVector n)

eqBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
  -> Bool
eqBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (==) @(Pantomime.BitVector n)

neqBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
  -> Bool
neqBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (/=) @(Pantomime.BitVector n)

ltBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
  -> Bool
ltBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (<) @(Pantomime.BitVector n)

leBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
  -> Bool
leBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (<=) @(Pantomime.BitVector n)

gtBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
  -> Bool
gtBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (>) @(Pantomime.BitVector n)

geBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> BitVector n
  -> Bool
geBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv n -> Bool
    go = coerce $ (>=) @(Pantomime.BitVector n)

shiftLBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> Int
  -> BitVector n
shiftLBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> Int -> bv n
    go = coerce $ shiftL @(Pantomime.BitVector n)

shiftRBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> Int
  -> BitVector n
shiftRBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> Int -> bv n
    go = coerce $ shiftR @(Pantomime.BitVector n)

fromIntegerBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => Natural
  -> Integer
  -> BitVector n
fromIntegerBitVector _ = go
  where
    go :: Coercible bv Pantomime.BitVector => Integer -> bv n
    go = coerce $ fromInteger @(Pantomime.BitVector n)

sizeBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> Int
sizeBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> Int
    go = coerce $ finiteBitSize @(Pantomime.BitVector n)

concatBitVector
  :: forall m n
   . KnownNat m
  => Coercible BitVector Pantomime.BitVector
  => BitVector n
  -> BitVector m
  -> BitVector (n + m)
concatBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> bv m -> bv (n + m)
    go = coerce Pantomime.concat

type BitVector1 = Pantomime.BitVector 1

unpackBitVector
  :: Coercible BitVector Pantomime.BitVector
  => Coercible Bit BitVector1
  => BitVector 1
  -> Bit
unpackBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => Coercible bit BitVector1 => bv 1 -> bit
    go = coerce

packBitVector
  :: Coercible BitVector Pantomime.BitVector
  => Coercible Bit BitVector1
  => Bit
  -> BitVector 1
packBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => Coercible bit BitVector1 => bit -> bv 1
    go = coerce

xToBVBitVector
  :: KnownNat n
  => BitVector n
  -> BitVector n
xToBVBitVector = id

msbBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => Coercible Bit BitVector1
  => KnownNat n
  => BitVector n
  -> Bit
msbBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => Coercible bit BitVector1 => bv n -> bit
    go = coerce msb

    msb :: Pantomime.BitVector n -> Pantomime.BitVector 1
    -- msb = case leqNat @1 @n of
    --   Just Dict -> Pantomime.select @0
    --   Nothing -> undefined
    -- TODO: Yes this is wrong: what is the msb of an empty bitvector. I'll just
    -- leave it as is for now, assuming the bad case isn't reached. We don't
    -- support comparison on Natural for now, so this is the stop-gap solution.
    msb = case unsafeDict @(1 <= n) of Dict -> Pantomime.select @0

sliceBitVector
  :: forall upper top idx
   . Coercible BitVector Pantomime.BitVector
  => BitVector (upper + 1 + top)
  -> SNat upper
  -> SNat idx
  -> BitVector (upper + 1 - idx)
sliceBitVector x SNat {} SNat {} = go x
  where
    go :: Coercible bv Pantomime.BitVector => bv (upper + 1 + top) -> bv (upper + 1 - idx)
    go = coerce $ Pantomime.stupidSlice @upper @top @idx
  -- where
  --   go :: Coercible bv Pantomime.BitVector => bv (upper + 1 + top) -> bv (upper + 1 - idx)
  --   go = coerce sel

  --   sel :: Pantomime.BitVector (upper + 1 + top) -> Pantomime.BitVector (upper + 1 - idx)
  --   sel x' = runIdentity do
  --     Dict <- pure $ Pantomime.withNat x' (Dict @(KnownNat (upper + 1 + top)))
  --     SomeNat' @upper1 <- pure $ typeAdd @upper @1
  --     SomeNat' @width <- pure $ typeSub @upper @idx
  --     -- typeSub
  --     Dict <- pure $ unsafeDict @(upper + 1 - idx ~ width)
  --     Dict <- pure $ unsafeDict @(idx + width <= upper + 1 + top)

  --     pure $ Pantomime.select @idx @width @(upper + 1 + top) x'

minBoundBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => BitVector n
minBoundBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n
    go = coerce Pantomime.stupidMinBound

toIntegerBitVector
  :: forall n
   . Coercible BitVector Pantomime.BitVector
  => KnownNat n
  => BitVector n
  -> Integer
toIntegerBitVector = go
  where
    go :: Coercible bv Pantomime.BitVector => bv n -> Integer
    go = coerce Pantomime.toInteger

eqBit :: Coercible Bit BitVector1 => Bit -> Bit -> Bool
eqBit = go
  where
    go :: Coercible bit BitVector1 => bit -> bit -> Bool
    go = coerce $ (==) @BitVector1

neqBit :: Coercible Bit BitVector1 => Bit -> Bit -> Bool
neqBit = go
  where
    go :: Coercible bit BitVector1 => bit -> bit -> Bool
    go = coerce $ (/=) @BitVector1

highBit :: Coercible Bit BitVector1 => Bit
highBit = go
  where
    go :: Coercible bit BitVector1 => bit
    go = coerce @BitVector1 $ 1

lowBit :: Coercible Bit BitVector1 => Bit
lowBit = go
  where
    go :: Coercible bit BitVector1 => bit
    go = coerce @BitVector1 $ 0

axioms :: PluginAxioms
axioms = PluginAxioms
  { typeAxioms = fromList
    [ (''Signed, ''Pantomime.BitVector)
    , (''Unsigned, ''Pantomime.BitVector)
    , (''BitVector, ''Pantomime.BitVector)
    , (''Bit, ''BitVector1)
    ]
  , termAxioms = fromList
    [ ('(Signed.+#), 'plusSigned)
    , ('(Signed.-#), 'subSigned)
    , ('(Signed.*#), 'mulSigned)
    , ('Signed.negate#, 'negateSigned)
    , ('Signed.complement#, 'complementSigned)
    , ('Signed.and#, 'andSigned)
    , ('Signed.or#, 'orSigned)
    , ('Signed.xor#, 'xorSigned)
    , ('Signed.abs#, 'absSigned)
    , ('Signed.eq#, 'eqSigned)
    , ('Signed.neq#, 'neqSigned)
    , ('Signed.lt#, 'ltSigned)
    , ('Signed.le#, 'leSigned)
    , ('Signed.gt#, 'gtSigned)
    , ('Signed.ge#, 'geSigned)
    , ('Signed.shiftL#, 'shiftLSigned)
    , ('Signed.shiftR#, 'shiftRSigned)
    , ('Signed.fromInteger#, 'fromIntegerSigned)
    , ('Signed.unpack#, 'unpackSigned)
    , ('Signed.pack#, 'packSigned)
    , ('Signed.size#, 'sizeSigned)
    , ('Signed.resize#, 'resizeSigned)

    , ('(Unsigned.+#), 'plusUnsigned)
    , ('(Unsigned.-#), 'subUnsigned)
    , ('(Unsigned.*#), 'mulUnsigned)
    , ('Unsigned.negate#, 'negateUnsigned)
    , ('Unsigned.complement#, 'complementUnsigned)
    , ('Unsigned.and#, 'andUnsigned)
    , ('Unsigned.or#, 'orUnsigned)
    , ('Unsigned.xor#, 'xorUnsigned)
    , ('Unsigned.eq#, 'eqUnsigned)
    , ('Unsigned.neq#, 'neqUnsigned)
    , ('Unsigned.lt#, 'ltUnsigned)
    , ('Unsigned.le#, 'leUnsigned)
    , ('Unsigned.gt#, 'gtUnsigned)
    , ('Unsigned.ge#, 'geUnsigned)
    , ('Unsigned.shiftL#, 'shiftLUnsigned)
    , ('Unsigned.shiftR#, 'shiftRUnsigned)
    , ('Unsigned.fromInteger#, 'fromIntegerUnsigned)
    , ('Unsigned.unpack#, 'unpackUnsigned)
    , ('Unsigned.pack#, 'packUnsigned)
    , ('Unsigned.size#, 'sizeUnsigned)
    , ('Unsigned.resize#, 'resizeUnsigned)

    , ('(BitVector.+#), 'plusBitVector)
    , ('(BitVector.-#), 'subBitVector)
    , ('(BitVector.*#), 'mulBitVector)
    , ('BitVector.negate#, 'negateBitVector)
    , ('BitVector.complement#, 'complementBitVector)
    , ('BitVector.and#, 'andBitVector)
    , ('BitVector.or#, 'orBitVector)
    , ('BitVector.xor#, 'xorBitVector)
    , ('BitVector.eq#, 'eqBitVector)
    , ('BitVector.neq#, 'neqBitVector)
    , ('BitVector.lt#, 'ltBitVector)
    , ('BitVector.le#, 'leBitVector)
    , ('BitVector.gt#, 'gtBitVector)
    , ('BitVector.ge#, 'geBitVector)
    , ('BitVector.shiftL#, 'shiftLBitVector)
    , ('BitVector.shiftR#, 'shiftRBitVector)
    , ('BitVector.fromInteger#, 'fromIntegerBitVector)
    , ('BitVector.unpack#, 'unpackBitVector)
    , ('BitVector.pack#, 'packBitVector)
    , ('BitVector.size#, 'sizeBitVector)
    , ('BitVector.xToBV, 'xToBVBitVector)
    , ('Bit.msb#, 'msbBitVector)
    , ('BitVector.toInteger#, 'toIntegerBitVector)
    , ('BitVector.slice#, 'sliceBitVector)
    , ('(BitVector.++#), 'concatBitVector)
    , ('BitVector.minBound#, 'minBoundBitVector)

    , ('Bit.eq##, 'eqBit)
    , ('Bit.neq##, 'neqBit)
    , ('Bit.high, 'highBit)
    , ('Bit.low, 'lowBit)
    ]
  }
