{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE GADTs #-}

module Pantomime.Grisette.SizedBV
  ( SizedBV (..)
  , sizedBVExtract
  , sizedBVResize
  , sizedBVZresize
  , sizedBVSresize
  ) where

import GHC.TypeNats (type (<=), type (+), type (-), KnownNat)

import Data.Type.Ord (OrderingI (..))

import Control.Monad.Identity (runIdentity)

import Pantomime.Dict

-- | Sized bit vector operations.
--
-- Including concatenation ('sizedBVConcat'), extension ('sizedBVZext',
-- 'sizedBVSext', 'sizedBVExt'), and selection ('sizedBVSelect').
class SizedBV bv where
  -- | Concatenation of two bit vectors.
  sizedBVConcat
    :: forall l r
     . KnownNat l
    => KnownNat r
    => bv l
    -> bv r
    -> bv (l + r)

  -- | Zero extension of a bit vector.
  sizedBVZext
    :: forall l r
     . KnownNat l
    => KnownNat r
    => l <= r
    => bv l
    -> bv r

  -- | Signed extension of a bit vector.
  sizedBVSext
    :: forall l r
     . KnownNat l
    => KnownNat r
    => l <= r
    => bv l
    -> bv r

  -- | Extension of a bit vector.
  --
  -- Signedness is determined by the input bit vector type.
  sizedBVExt
    :: forall l r
     . KnownNat l
    => KnownNat r
    => l <= r
    => bv l
    -> bv r

  -- | Slicing out a smaller bit vector from a larger one, selecting a slice
  -- with width @width@ starting from index @idx@.
  --
  -- The least significant bit is indexed as 0.
  sizedBVSelect
    :: forall idx width n
     . KnownNat idx
    => KnownNat width
    => KnownNat n
    => idx + width <= n
    => bv n
    -> bv width

-- | Slicing out a smaller bit vector from a larger one, extract a slice from
-- bit i down to j.
--
-- The least significant bit is indexed as 0.
sizedBVExtract
  :: forall bv end start n
   . SizedBV bv
  => KnownNat start
  => KnownNat end
  => KnownNat n
  => end <= n
  => bv n
  -> bv (end - start)
sizedBVExtract = runIdentity $ do
  -- SAFETY: This is always true as we know: end <= n
  Dict <- pure $ unsafeDict @(start + (end - start) ~ end)
  SomeNat' @width <- pure $ typeSub @end @start

  pure $ sizedBVSelect @bv @start @width @n

-- | Helper functions to implement the flavours of resizing.
sizedBVResizeWith
  :: forall bv l r
   . SizedBV bv
  => KnownNat l
  => KnownNat r
  => (l <= r => bv l -> bv r)
  -> bv l
  -> bv r
sizedBVResizeWith f = case cmpNat' @l @r of
  LTI -> f
  EQI -> id
  -- SAFETY: The unsafe coerce is just to have 'r <= l' as Haskell cannot figure
  -- this out given the 'l >= r' that is already in context. Theoretically we
  -- should be able to do this without unsafeCoerce, but I'm not sure how.
  -- I'm not keen on importing a type level nat plugin for just one function.
  GTI -> case unsafeDict @(r <= l) of
    Dict -> sizedBVSelect @bv @0

-- | Resize the given bitvector.
--
-- Whether the bitvector is sign extended or not depends on its implementation
-- of 'sizedBVExt'.
sizedBVResize
  :: forall bv l r
   . SizedBV bv
  => KnownNat l
  => KnownNat r
  => bv l
  -> bv r
sizedBVResize = sizedBVResizeWith sizedBVExt

-- | Resize the given bitvector.
--
-- Will zero extend the bitvector if it is extended.
sizedBVZresize
  :: forall bv l r
   . SizedBV bv
  => KnownNat l
  => KnownNat r
  => bv l
  -> bv r
sizedBVZresize = sizedBVResizeWith sizedBVZext

-- | Resize the given bitvector.
--
-- Will sign extend the bitvector if it is extended.
sizedBVSresize
  :: forall bv l r
   . SizedBV bv
  => KnownNat l
  => KnownNat r
  => bv l
  -> bv r
sizedBVSresize = sizedBVResizeWith sizedBVSext
