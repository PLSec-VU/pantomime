{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UnliftedDatatypes #-}

-- TODO: Perhaps 'Base' would be better than 'BuiltIn', because not everything
-- here is necessarily built-in.
--
-- TODO: A lot of functions here should still get a Haskell implementation that
-- mirrors the symbolic behaviour.
-- WARNING: Helper functions should only interact with primitive data types
-- via the primitive functions that are marked as 'OPAQUE'. These primitive
-- functions are interpreted in the backend of symbolic executor. Any direct
-- unwrapping of 'Bool' will crash the execution if it is reached.
--
-- Many of the helper functions will look verbose and are written in a somewhat
-- roundabout way. This is intentional, do not change them unless you know what
-- you're doing!
module Pantomime.BuiltIn
  -- | Embeddable constraint for user interpretations.
  ( Embeddable (..)

  -- | Typeclass to differentiate primitive types.
  , Primitive

  -- | Built-in literal conversion functions.
  --
  -- WARNING: These functions should not be called directly. Their purpose is
  -- to receive an interpretation such that the symbolic engine knows how to
  -- construct these literals from GHC Core.
  , PlatformWordSize
  , toInt#
  , toInt8#
  , toInt16#
  , toInt32#
  , toInt64#
  , toWord#
  , toWord8#
  , toWord16#
  , toWord32#
  , toWord64#
  , eqInt#
  , eqInt8#
  , eqInt16#
  , eqInt32#
  , eqInt64#
  , eqWord#
  , eqWord8#
  , eqWord16#
  , eqWord32#
  , eqWord64#

  -- | System Fc operations.
  , ite
  , iteIP
  , iteI8
  , iteI16
  , iteI32
  , iteI64
  , iteWP
  , iteW8
  , iteW16
  , iteW32
  , iteW64
  , tagToEnum
  , dataToTag
  , raise

  -- | Boolean operations.
  , Bool (True, False)
  , true
  , false
  , not
  , (&&)
  , (||)
  , implies
  , xor
  , iff

  -- | Integer operations.
  , Integer
  , ineg
  , iabs
  , iadd
  , imul
  , idiv
  , imod
  , ieq
  , ineq
  , ile
  , ilt

  -- | Bit-vector operations.
  , BitVec
  , bvnot
  , bvneg
  , bvand
  , bvor
  , bvxor
  , bvadd
  , bvmul
  , bvudiv
  , bvsdiv
  , bvurem
  , bvsrem
  , bvshl
  , bvlshr
  , bvashr
  , bveq
  , bvneq
  , bvule
  , bvsle
  , bvult
  , bvslt
  , bvconcat
  , bvzext
  , bvsext
  , bvselect

  -- | Array operations.
  , Array
  , aconst
  , aselect
  , astore
  ) where

import Data.Coerce (coerce)
import GHC.Base
  ( TYPE
  , RuntimeRep (..)
  , Int#
  , Int8#
  , Int16#
  , Int32#
  , Int64#
  , Word#
  , Word8#
  , Word16#
  , Word32#
  , Word64#
  , Constraint
  , Type
  )
import GHC.TypeLits (TypeError, ErrorMessage (..))
import GHC.TypeNats (Nat, KnownNat, type (+), type (<=))
import Prelude qualified
import Prelude (($))

class Private a b

-- TODO: At some point I want this typeclass to have behaviour like 'Coercible'.
-- For now, I'll leave it like this as it eases the implementation quite a bit.
class Private a b => Embeddable (a :: TYPE r1) (b :: TYPE r2) where
  embed :: a -> b
  project :: b -> a

-- class Private a b => Embeddable (a :: k1) (b :: k2)

-- embed
--   :: forall {r1} {r2} (a :: TYPE r1) (b :: TYPE r2)
--    . Embeddable a b
--   => a
--   -> b
-- embed = embed

type family Primitive a :: Constraint where
  Primitive Bool = ()
  Primitive Integer = ()
  Primitive (BitVec n) = 1 <= n
  Primitive (Array k v) = (Primitive k, Primitive v)
  Primitive x = TypeError ('Text "'" :<>: ShowType x :<>: 'Text "' is not a primitive type")

-- TODO: For now, we'll just have the platform sized as 64-bit. Not sure how
-- we would handle this correctly? Maybe with a pragma?
type PlatformWordSize = 64

-- | Literal construction function for built-in Haskell 'Int#' literal. Note
-- that
{-# OPAQUE toInt# #-}
toInt# :: BitVec PlatformWordSize -> Int#
toInt# = toInt#

{-# OPAQUE toInt8# #-}
toInt8# :: BitVec 8 -> Int8#
toInt8# = toInt8#

{-# OPAQUE toInt16# #-}
toInt16# :: BitVec 16 -> Int16#
toInt16# = toInt16#

{-# OPAQUE toInt32# #-}
toInt32# :: BitVec 32 -> Int32#
toInt32# = toInt32#

{-# OPAQUE toInt64# #-}
toInt64# :: BitVec 64 -> Int64#
toInt64# = toInt64#

{-# OPAQUE toWord# #-}
toWord# :: BitVec PlatformWordSize -> Word#
toWord# = toWord#

{-# OPAQUE toWord8# #-}
toWord8# :: BitVec 8 -> Word8#
toWord8# = toWord8#

{-# OPAQUE toWord16# #-}
toWord16# :: BitVec 16 -> Word16#
toWord16# = toWord16#

{-# OPAQUE toWord32# #-}
toWord32# :: BitVec 32 -> Word32#
toWord32# = toWord32#

{-# OPAQUE toWord64# #-}
toWord64# :: BitVec 64 -> Word64#
toWord64# = toWord64#

{-# OPAQUE eqInt# #-}
eqInt# :: Int# -> Int# -> Bool
eqInt# = eqInt#

{-# OPAQUE eqInt8# #-}
eqInt8# :: Int8# -> Int8# -> Bool
eqInt8# = eqInt8#

{-# OPAQUE eqInt16# #-}
eqInt16# :: Int16# -> Int16# -> Bool
eqInt16# = eqInt16#

{-# OPAQUE eqInt32# #-}
eqInt32# :: Int32# -> Int32# -> Bool
eqInt32# = eqInt32#

{-# OPAQUE eqInt64# #-}
eqInt64# :: Int64# -> Int64# -> Bool
eqInt64# = eqInt64#

{-# OPAQUE eqWord# #-}
eqWord# :: Word# -> Word# -> Bool
eqWord# = eqWord#

{-# OPAQUE eqWord8# #-}
eqWord8# :: Word8# -> Word8# -> Bool
eqWord8# = eqWord8#

{-# OPAQUE eqWord16# #-}
eqWord16# :: Word16# -> Word16# -> Bool
eqWord16# = eqWord16#

{-# OPAQUE eqWord32# #-}
eqWord32# :: Word32# -> Word32# -> Bool
eqWord32# = eqWord32#

{-# OPAQUE eqWord64# #-}
eqWord64# :: Word64# -> Word64# -> Bool
eqWord64# = eqWord64#

-- TODO: There is no real way to implement 'ite', 'tagToEnum' and 'dataToTag'
-- non-native. Maybe we could have their Haskell implementation given by a
-- plugin? For now, we can just skip it. Alternatively, we need to expose ite
-- for every representation separately...

-- | Primitive if-then-else construct.
{-# OPAQUE ite #-}
ite :: Bool -> a -> a -> a
ite (Bool scrut) tr fl = case scrut of
  Prelude.True -> tr
  Prelude.False -> fl

data IP (a :: TYPE IntRep) where
  IP :: a -> IP a

iteIP :: forall (a :: TYPE IntRep). Bool -> a -> a -> a
iteIP scrut tr fl = let !(IP value) = ite scrut (IP tr) (IP fl) in value

data I8 (a :: TYPE Int8Rep) where
  I8 :: a -> I8 a

iteI8 :: forall (a :: TYPE Int8Rep). Bool -> a -> a -> a
iteI8 scrut tr fl = let !(I8 value) = ite scrut (I8 tr) (I8 fl) in value

data I16 (a :: TYPE Int16Rep) where
  I16 :: a -> I16 a

iteI16 :: forall (a :: TYPE Int16Rep). Bool -> a -> a -> a
iteI16 scrut tr fl = let !(I16 value) = ite scrut (I16 tr) (I16 fl) in value

data I32 (a :: TYPE Int32Rep) where
  I32 :: a -> I32 a

iteI32 :: forall (a :: TYPE Int32Rep). Bool -> a -> a -> a
iteI32 scrut tr fl = let !(I32 value) = ite scrut (I32 tr) (I32 fl) in value

data I64 (a :: TYPE Int64Rep) where
  I64 :: a -> I64 a

iteI64 :: forall (a :: TYPE Int64Rep). Bool -> a -> a -> a
iteI64 scrut tr fl = let !(I64 value) = ite scrut (I64 tr) (I64 fl) in value

data WP (a :: TYPE WordRep) where
  WP :: a -> WP a

iteWP :: forall (a :: TYPE WordRep). Bool -> a -> a -> a
iteWP scrut tr fl = let !(WP value) = ite scrut (WP tr) (WP fl) in value

data W8 (a :: TYPE Word8Rep) where
  W8 :: a -> W8 a

iteW8 :: forall (a :: TYPE Word8Rep). Bool -> a -> a -> a
iteW8 scrut tr fl = let !(W8 value) = ite scrut (W8 tr) (W8 fl) in value

data W16 (a :: TYPE Word16Rep) where
  W16 :: a -> W16 a

iteW16 :: forall (a :: TYPE Word16Rep). Bool -> a -> a -> a
iteW16 scrut tr fl = let !(W16 value) = ite scrut (W16 tr) (W16 fl) in value

data W32 (a :: TYPE Word32Rep) where
  W32 :: a -> W32 a

iteW32 :: forall (a :: TYPE Word32Rep). Bool -> a -> a -> a
iteW32 scrut tr fl = let !(W32 value) = ite scrut (W32 tr) (W32 fl) in value

data W64 (a :: TYPE Word64Rep) where
  W64 :: a -> W64 a

iteW64 :: forall (a :: TYPE Word64Rep). Bool -> a -> a -> a
iteW64 scrut tr fl = let !(W64 value) = ite scrut (W64 tr) (W64 fl) in value

-- | Tag to enumeration conversion with the intent to match 'tagToEnum#'.
--
-- WARNING: We cannot enforce that the polymorphic value is indeed an
-- enumeration, unlike the real 'tagToEnum#'. Hence, this function is incredibly
-- unsafe.
{-# OPAQUE tagToEnum #-}
tagToEnum :: forall a. BitVec PlatformWordSize -> a
tagToEnum = tagToEnum

-- | Returns the index (starting at zero) of the constructor used to produce
-- the given argument.
{-# OPAQUE dataToTag #-}
dataToTag :: forall l (a :: TYPE (BoxedRep l)). a -> BitVec PlatformWordSize
dataToTag = dataToTag

-- | Raise a error in the Haskell runtime.
{-# OPAQUE raise #-}
raise :: forall {l} {r} (a :: TYPE (BoxedRep l)) (b :: TYPE r). a -> b
raise = raise

-- TODO: We should provide implementations for many of the common typeclasses.
-- For now, this suffices.
-- TODO: Another thing to look into is conversion between primitive types. Idk
-- if there for example is a primitive operation to convert between an boolean
-- and a single-bit bitvector.
-- | Pantomime primitive Boolean.
newtype Bool where
  Bool :: Prelude.Bool -> Bool

{-# OPAQUE true #-}
true :: Bool
true = coerce Prelude.True

{-# OPAQUE false #-}
false :: Bool
false = coerce Prelude.False

{-# OPAQUE not #-}
not :: Bool -> Bool
not = coerce Prelude.not

{-# OPAQUE (&&) #-}
(&&) :: Bool -> Bool -> Bool
(&&) = coerce (Prelude.&&)

{-# OPAQUE (||) #-}
(||) :: Bool -> Bool -> Bool
(||) = coerce (Prelude.||)

{-# OPAQUE implies #-}
implies :: Bool -> Bool -> Bool
implies = coerce \lhs rhs -> Prelude.not lhs Prelude.|| rhs

{-# OPAQUE xor #-}
xor :: Bool -> Bool -> Bool
xor = coerce $ (Prelude./=) @Prelude.Bool

{-# OPAQUE iff #-}
iff :: Bool -> Bool -> Bool
iff = coerce $ (Prelude.==) @Prelude.Bool

pattern True :: Bool
pattern True <- (convert -> Prelude.True)
  where
    True = true

pattern False :: Bool
pattern False <- (convert -> Prelude.False)
  where
    False = false

{-# COMPLETE True, False #-}

-- TODO: I dislike this name. Not sure what a better alternative is.
-- | Convert a symbolic Boolean to the standard Haskell Boolean.
convert :: Bool -> Prelude.Bool
convert value = ite value Prelude.True Prelude.False

-- | Pantomime primitive integer.
newtype Integer where
  Integer :: Prelude.Integer -> Integer

{-# OPAQUE ineg #-}
ineg :: Integer -> Integer
ineg = ineg

{-# OPAQUE iabs #-}
iabs :: Integer -> Integer
iabs = iabs

{-# OPAQUE iadd #-}
iadd :: Integer -> Integer -> Integer
iadd = coerce $ (Prelude.+) @Prelude.Integer

{-# OPAQUE imul #-}
imul :: Integer -> Integer -> Integer
imul = imul

{-# OPAQUE idiv #-}
idiv :: Integer -> Integer -> Integer
idiv = idiv

{-# OPAQUE imod #-}
imod :: Integer -> Integer -> Integer
imod = imod

{-# OPAQUE ieq #-}
ieq :: Integer -> Integer -> Bool
ieq = ieq

{-# OPAQUE ineq #-}
ineq :: Integer -> Integer -> Bool
ineq = ineq

{-# OPAQUE ile #-}
ile :: Integer -> Integer -> Bool
ile = ile

{-# OPAQUE ilt #-}
ilt :: Integer -> Integer -> Bool
ilt = ilt

-- instance Num Integer where
--   (+) = plusInteger
--   (*) = timesInteger
--   abs = absInteger
--   signum = signumInteger
--   negate = negateInteger
--   fromInteger = fromIntegerInteger

-- | Pantomime primitive bitvector.
data BitVec (n :: Nat) where
  -- BitVec :: KnownPos n => Util.BitVec n -> BitVec n

type role BitVec nominal

{-# OPAQUE bvnot #-}
bvnot :: forall n. BitVec n -> BitVec n
bvnot = bvnot

{-# OPAQUE bvneg #-}
bvneg :: forall n. BitVec n -> BitVec n
bvneg = bvneg

{-# OPAQUE bvand #-}
bvand :: forall n. BitVec n -> BitVec n -> BitVec n
bvand = bvand

{-# OPAQUE bvor #-}
bvor :: forall n. BitVec n -> BitVec n -> BitVec n
bvor = bvor

{-# OPAQUE bvxor #-}
bvxor :: forall n. BitVec n -> BitVec n -> BitVec n
bvxor = bvxor

{-# OPAQUE bvadd #-}
bvadd :: forall n. BitVec n -> BitVec n -> BitVec n
bvadd = bvadd

{-# OPAQUE bvmul #-}
bvmul :: forall n. BitVec n -> BitVec n -> BitVec n
bvmul = bvmul

{-# OPAQUE bvudiv #-}
bvudiv :: forall n. BitVec n -> BitVec n -> BitVec n
bvudiv = bvudiv

{-# OPAQUE bvsdiv #-}
bvsdiv :: forall n. BitVec n -> BitVec n -> BitVec n
bvsdiv = bvsdiv

{-# OPAQUE bvurem #-}
bvurem :: forall n. BitVec n -> BitVec n -> BitVec n
bvurem = bvurem

{-# OPAQUE bvsrem #-}
bvsrem :: forall n. BitVec n -> BitVec n -> BitVec n
bvsrem = bvsrem

{-# OPAQUE bvshl #-}
bvshl :: forall n. BitVec n -> BitVec n -> BitVec n
bvshl = bvshl

{-# OPAQUE bvlshr #-}
bvlshr :: forall n. BitVec n -> BitVec n -> BitVec n
bvlshr = bvlshr

{-# OPAQUE bvashr #-}
bvashr :: forall n. BitVec n -> BitVec n -> BitVec n
bvashr = bvashr

{-# OPAQUE bveq #-}
bveq :: forall n. BitVec n -> BitVec n -> Bool
bveq = bveq

{-# OPAQUE bvneq #-}
bvneq :: forall n. BitVec n -> BitVec n -> Bool
bvneq = bvneq

{-# OPAQUE bvule #-}
bvule :: forall n. BitVec n -> BitVec n -> Bool
bvule = bvule

{-# OPAQUE bvsle #-}
bvsle :: forall n. BitVec n -> BitVec n -> Bool
bvsle = bvsle

{-# OPAQUE bvult #-}
bvult :: forall n. BitVec n -> BitVec n -> Bool
bvult = bvult

{-# OPAQUE bvslt #-}
bvslt :: forall n. BitVec n -> BitVec n -> Bool
bvslt = bvslt

{-# OPAQUE bvconcat #-}
bvconcat :: forall l r. BitVec l -> BitVec r -> BitVec (l + r)
bvconcat = bvconcat

{-# OPAQUE bvzext #-}
bvzext :: forall ext n. BitVec n -> BitVec (ext + n)
bvzext = bvzext

{-# OPAQUE bvsext #-}
bvsext :: forall ext n. BitVec n -> BitVec (ext + n)
bvsext = bvzext

{-# OPAQUE bvselect #-}
bvselect
  :: forall idx width n
   . KnownNat idx
  => KnownNat width
  => 1 <= width
  => idx + width <= n
  => BitVec n
  -> BitVec width
bvselect = bvselect @idx

data Array (k :: Type) (v :: Type)

{-# OPAQUE aconst #-}
aconst :: forall k v. Primitive k => Primitive v => v -> Array k v
aconst = aconst

{-# OPAQUE aselect #-}
aselect :: forall k v. Primitive k => Primitive v => Array k v -> k -> v
aselect = aselect

{-# OPAQUE astore #-}
astore
  :: forall k v
   . Primitive k
  => Primitive v
  => Array k v
  -> k
  -> v
  -> Array k v
astore = astore
