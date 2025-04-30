{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}

module Symbolic.Sized.Class
  ( SizedBV' (..)
  , sizedBVSelect'
  ) where
import GHC.TypeNats (type (<=), type (+), KnownNat)
import Data.Data (Proxy(..))

-- | Sized bit vector operations.
--
-- Including concatenation ('sizedBVConcat'), extension ('sizedBVZext',
-- 'sizedBVSext', 'sizedBVExt'), and selection ('sizedBVSelect').
class SizedBV' bv where
  -- | Concatenation of two bit vectors.
  sizedBVConcat'
    :: forall l r
     . KnownNat l
    => KnownNat r
    => bv l
    -> bv r
    -> bv (l + r)

  -- | Zero extension of a bit vector.
  sizedBVZext'
    :: forall l r
     . KnownNat l
    => KnownNat r
    => l <= r
    => bv l
    -> bv r

  -- | Signed extension of a bit vector.
  sizedBVSext'
    :: forall l r
     . KnownNat l
    => KnownNat r
    => l <= r
    => bv l
    -> bv r

  -- | Extension of a bit vector.
  --
  -- Signedness is determined by the input bit vector type.
  sizedBVExt'
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
  sizedBVSelect''
    :: forall idx width n
     . KnownNat idx
    => KnownNat width
    => KnownNat n
    => idx + width <= n
    => Proxy idx
    -> Proxy width
    -> bv n
    -> bv width

sizedBVSelect'
  :: forall bv idx width n
   . SizedBV' bv
  => KnownNat idx
  => KnownNat width
  => KnownNat n
  => idx + width <= n
  => bv n
  -> bv width
sizedBVSelect' = sizedBVSelect'' @_ @idx Proxy Proxy

-- TODO: We could implement sizedBVExtract using sizedBVSelect.

-- TODO: Move sizedBVResize here!
