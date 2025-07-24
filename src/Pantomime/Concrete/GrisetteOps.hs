{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ExtendedLiterals #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UnliftedDatatypes #-}

module Pantomime.Concrete.GrisetteOps
  ( Bool# (..)
  , not#
  , (&&#)
  , (||#)

  , GHC.Int8#
  , GHC.Int16#
  , GHC.Int32#
  , GHC.Int64#
  , GrisetteEq (..)
  , GrisetteOrd (..)
  , GrisetteBits (..)
  , GrisetteNum (..)
  ) where

import Prelude (($), otherwise)

import GHC.Base qualified as GHC

-- | Primitive boolean.
--
-- Importantly, it is unlifted, which means it matches Grisette boolean
-- evaluation semantics.
data Bool# :: GHC.UnliftedType where
  False# :: Bool#
  True# :: Bool#

-- | Conversion from Int# to Bool#.
intToBool#
  :: GHC.Int#
  -> Bool#
intToBool# = \case
  0# -> False#
  _ -> True#

-- | Primitive boolean 'not'.
not#
  :: Bool#
  -> Bool#
not# = \case
  False# -> True#
  _ -> False#

-- | Primitive boolean 'and'.
(&&#)
  :: Bool#
  -> Bool#
  -> Bool#
(&&#) l r = case l of
  True# -> r
  _ -> False#

-- | Primitive boolean 'or'.
(||#)
  :: Bool#
  -> Bool#
  -> Bool#
(||#) l r = case l of
  False# -> r
  _ -> True#

{-# INLINE shiftMask #-}
shiftMask :: GHC.Int# -> GHC.Int# -> GHC.Int#
shiftMask m b = GHC.negateInt# (b GHC.<# m)

-- | Equality operators supported by Grisette.
class GrisetteEq (a :: GHC.TYPE r) where
  (==#) :: a -> a -> Bool#
  (/=#) :: a -> a -> Bool#

  infix 4 ==#
  infix 4 /=#

-- | Ordering operators supported by Grisette.
class GrisetteEq a => GrisetteOrd (a :: GHC.TYPE r) where
  (<#) :: a -> a -> Bool#
  (<=#) :: a -> a -> Bool#

  infix 4 <#
  infix 4 <=#

-- | Bitwise operators supported by Grisette.
class GrisetteEq a => GrisetteBits (a :: GHC.TYPE r) where
  (.&.#) :: a -> a -> a
  (.|.#) :: a -> a -> a
  (.^.#) :: a -> a -> a
  complement# :: a -> a
  shiftL# :: a -> a -> a
  -- | Grisette only supports a single type of shift.
  --
  -- Whether it is an arithmetic or logical shift depends on signedness of the
  -- type.
  shiftR# :: a -> a -> a
  rotateL# :: a -> a -> a
  rotateR# :: a -> a -> a

  infixl 7 .&.#
  infixl 5 .|.#
  infixl 6 .^.#

-- | Numeric operators supported by Grisette.
class GrisetteNum (a :: GHC.TYPE r) where
  (+#) :: a -> a -> a
  (*#) :: a -> a -> a
  negate# :: a -> a
  abs# :: a -> a
  signum# :: a -> a

  infixl 6 +#
  infixl 7 *#

instance GrisetteEq GHC.Int64# where
  (==#) l r = intToBool# $ GHC.eqInt64# l r
  (/=#) l r = intToBool# $ GHC.neInt64# l r

instance GrisetteOrd GHC.Int64# where
  (<#) l r = intToBool# $ GHC.ltInt64# l r
  (<=#) l r = intToBool# $ GHC.leInt64# l r

-- | Helper to perform binary Word64# operations on Int64#.
binaryInt64#
  :: (GHC.Word64# -> GHC.Word64# -> GHC.Word64#)
  -> GHC.Int64#
  -> GHC.Int64#
  -> GHC.Int64#
binaryInt64# f lhs rhs = do
  let lhs' = GHC.int64ToWord64# lhs
  let rhs' = GHC.int64ToWord64# rhs
  GHC.word64ToInt64# $ f lhs' rhs'

unaryInt64#
  :: (GHC.Word64# -> GHC.Word64#)
  -> GHC.Int64#
  -> GHC.Int64#
unaryInt64# f x = GHC.word64ToInt64# $ f (GHC.int64ToWord64# x)

shiftInt64#
  :: (GHC.Int64# -> GHC.Int# -> GHC.Int64#)
  -- ^ Shift operation.
  -> GHC.Int64#
  -> GHC.Int64#
  -> GHC.Int64#
shiftInt64# f x i = do
  let i' = GHC.int64ToInt# i
  let mask = GHC.intToInt64# $ shiftMask 64# i'
  let shift = f x i'
  shift .&.# mask

rotateInt64#
  :: (GHC.Int64# -> GHC.Int# -> GHC.Int64#)
  -- ^ Logical shift forward direction.
  -> (GHC.Int64# -> GHC.Int# -> GHC.Int64#)
  -- ^ Logical Shift backward direction.
  -> GHC.Int64#
  -> GHC.Int64#
  -> GHC.Int64#
rotateInt64# fw bw x i = do
  let i' = GHC.word2Int# $ GHC.and# 63## (GHC.int2Word# $ GHC.int64ToInt# i)
  let shifted = fw x i'
  let rotated = bw x $ 64# GHC.-# i'
  shifted .|.# rotated

instance GrisetteBits GHC.Int64# where
  (.&.#) = binaryInt64# GHC.and64#
  (.|.#) = binaryInt64# GHC.or64#
  (.^.#) = binaryInt64# GHC.xor64#
  complement# = unaryInt64# GHC.not64#
  shiftL# = shiftInt64# GHC.uncheckedIShiftL64#
  shiftR# = shiftInt64# GHC.uncheckedIShiftRA64#
  rotateL# = rotateInt64# GHC.uncheckedIShiftL64# GHC.uncheckedIShiftRL64#
  rotateR# = rotateInt64# GHC.uncheckedIShiftRL64# GHC.uncheckedIShiftL64#

instance GrisetteNum GHC.Int64# where
  (+#) = GHC.plusInt64#
  (*#) = GHC.timesInt64#
  negate# = GHC.negateInt64#
  abs# x = case 0#Int64 <=# x of
    True# -> x
    False# -> negate# x
  signum# x = if
    | True# <- 0#Int64 <# x -> 1#Int64
    | True# <- x ==# 0#Int64 -> 0#Int64
    | otherwise -> -1#Int64

-- class GrisetteBitCast (from :: TYPE r) (to :: TYPE r) where
--   TODO: BitCastOr is a bit weird. In Haskell, we do have other NaN values for
--   which we want accurate support no? I.e. casting back and forth should give
--   the same value? Grisette doesn't support this behaviour out of the box...
--   For now, let's just not support it. I don't want to introduce semantic
--   inconsistencies. The easiest solution is to have a feature flag, where we
--   enable this operation. Call it something like "incoherent-fp-casts".
--   Ideally though, we implement this operation without inconsinstencies. Not
--   sure how yet though...
--   bitCast :: from -> to
--   bitCastOr :: from -> to -> to
