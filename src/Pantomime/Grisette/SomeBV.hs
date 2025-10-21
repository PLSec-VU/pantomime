{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}

module Pantomime.Grisette.SomeBV
  ( SomeBV (..)
  ) where

import GHC.TypeNats
  ( KnownNat
  , SomeNat (..)
  )

import GHC.Utils.Outputable
  ( Outputable (..)
  , IsLine (..)
  )

import Pantomime.Grisette.Mergeable (impossible)

import Grisette
  ( Mergeable (..)
  , ToCon (..)
  , ToSym (..)
  , MergingStrategy (..)
  , wrapStrategy
  )

import Data.Typeable
  ( type (:~:) (..)
  , Proxy (..)
  , eqT
  )

data SomeBV bv where
  SomeBV :: KnownNat n => bv n -> SomeBV bv

instance (forall n. KnownNat n => Show (bv n)) => Show (SomeBV bv) where
  show (SomeBV value) = show value

-- FIXME: This should really use the inner Outputable instance.
instance (forall n. KnownNat n => Show (bv n)) => Outputable (SomeBV bv) where
  ppr = text . show

instance (forall n. KnownNat n => Mergeable (bv n)) => Mergeable (SomeBV bv) where
  rootStrategy = SortedStrategy
    (\(SomeBV @n _) -> SomeNat @n Proxy)
    (\(SomeNat @n _) -> wrapStrategy @(bv n)
      rootStrategy
      SomeBV
      \case SomeBV @m bv | Just Refl <- eqT @n @m -> bv ; _ -> impossible)

instance (forall n. KnownNat n => ToSym (bva n) (bvb n)) => ToSym (SomeBV bva) (SomeBV bvb) where
  toSym (SomeBV @n bv) = SomeBV @n $ toSym bv

instance (forall n. KnownNat n => ToCon (bva n) (bvb n)) => ToCon (SomeBV bva) (SomeBV bvb) where
  toCon (SomeBV @n bv) = SomeBV @n <$> toCon bv
