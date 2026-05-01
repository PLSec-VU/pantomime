{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

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
  , hsi2i
  , i2hsi

  -- | Operations on type-level natural numbers.
  --
  -- These mirror the original 'KnownNat' implementation up to the inner value
  -- being the builtin 'Integer' of the symbolic executor.
  , KnownNat (..)
  , natVal
  , SNat (SNat)
  , (%+)
  , (%-)
  , SomeNat (..)
  , someNatVal

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
  , i2bv
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
  , bv2i
  , bvsize
  , bvnat
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
  , bvzresize
  , bvsresize

  -- | Array operations.
  , Array
  , aconst
  , aselect
  , astore
  , aeq
  ) where

import Control.Monad.Identity (Identity (..))
import Data.Bits qualified as Prelude (Bits (..))
import Data.Coerce (coerce)
import Data.Constraint (HasDict (..))
import Data.Constraint.Unsafe qualified as Prelude (unsafeSNat)
import Data.Composition ((.:))
import Data.Constraint.Unsafe (unsafeAxiom)
import Data.Data (Proxy (..))
import Data.Hashable (Hashable (..))
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
  , Type
  , WithDict (..)
  , noinline
  )
import GHC.TypeLits qualified as Prelude (natVal)
import GHC.TypeNats (Nat, type (+), type (-), type (<=))
import GHC.TypeNats qualified as Prelude (KnownNat)
import Grisette (SymShift(..), SizedBV (..), IntN, SignConversion (..))
import Grisette.Internal.SymPrim.Array qualified as Grisette
import Pantomime.Dict (Dict (..), SomeNat' (..), typeAdd, unsafeEq)
import Pantomime.Util qualified as Util (BitVec)
import Prelude qualified
import Prelude (Applicative (..), Ordering (..), ($), (.))

-- TODO: I guess we could also make this a typeclass without variables?
class Private a

instance Private a

-- TODO: At some point I want this typeclass to have behaviour like 'Coercible'.
-- For now, I'll leave it like this as it eases the implementation quite a bit.
class (Private a, Private b) => Embeddable (a :: TYPE r1) (b :: TYPE r2) where
  embed :: a -> b
  project :: b -> a

-- class Private a b => Embeddable (a :: k1) (b :: k2)

-- embed
--   :: forall {r1} {r2} (a :: TYPE r1) (b :: TYPE r2)
--    . Embeddable a b
--   => a
--   -> b
-- embed = embed

-- FIXME: I think calling Hashable on the primitives will now break stuff, as it
-- uses the actual underlying representation...
--
-- The reason to have this for now is to be able to use the array primitives.
-- Ideally though, we have a way of getting the hashable on the inner values
-- without exposing the typeclass to the outside. If we do find a way, make sure
-- to remove all the 'Hashable' instances on the primitive types!
class (Private a, Hashable a) => Primitive a

instance Primitive Bool

instance Primitive Integer

instance (1 <= n) => Primitive (BitVec n)

instance (Primitive k, Primitive v) => Primitive (Array k v)

-- type family Primitive a :: Constraint where
--   Primitive Bool = ()
--   Primitive Integer = ()
--   Primitive (BitVec n) = 1 <= n
--   Primitive (Array k v) = (Primitive k, Primitive v)
--   Primitive x = TypeError ('Text "'" :<>: ShowType x :<>: 'Text "' is not a primitive type")

-- TODO: For now, we'll just have the platform sized as 64-bit. Not sure how
-- we would handle this correctly? Maybe with a pragma?
type PlatformWordSize = 64

-- | Literal construction function for built-in Haskell 'Int#' literal.
--
-- Note that this should not be used directly. Instead, this should get a user
-- interpretation that matches the representation for 'Int#' as given by the
-- user.
-- TODO: I guess the above is true for all these functions below. Perhaps we can
-- document this once and have the instances reference this?
--
-- Actually though, it would be good to have functions to switch between Haskell
-- and Pantomime types, as one would perhaps also want to use these if they
-- plan on actually using these primitives for some check.
{-# OPAQUE toInt# #-}
toInt# :: BitVec PlatformWordSize -> Int#
toInt# = noinline toInt#

{-# OPAQUE toInt8# #-}
toInt8# :: BitVec 8 -> Int8#
toInt8# = noinline toInt8#

{-# OPAQUE toInt16# #-}
toInt16# :: BitVec 16 -> Int16#
toInt16# = noinline toInt16#

{-# OPAQUE toInt32# #-}
toInt32# :: BitVec 32 -> Int32#
toInt32# = noinline toInt32#

{-# OPAQUE toInt64# #-}
toInt64# :: BitVec 64 -> Int64#
toInt64# = noinline toInt64#

{-# OPAQUE toWord# #-}
toWord# :: BitVec PlatformWordSize -> Word#
toWord# = noinline toWord#

{-# OPAQUE toWord8# #-}
toWord8# :: BitVec 8 -> Word8#
toWord8# = noinline toWord8#

{-# OPAQUE toWord16# #-}
toWord16# :: BitVec 16 -> Word16#
toWord16# = noinline toWord16#

{-# OPAQUE toWord32# #-}
toWord32# :: BitVec 32 -> Word32#
toWord32# = noinline toWord32#

{-# OPAQUE toWord64# #-}
toWord64# :: BitVec 64 -> Word64#
toWord64# = noinline toWord64#

{-# OPAQUE eqInt# #-}
eqInt# :: Int# -> Int# -> Bool
eqInt# = noinline eqInt#

{-# OPAQUE eqInt8# #-}
eqInt8# :: Int8# -> Int8# -> Bool
eqInt8# = noinline eqInt8#

{-# OPAQUE eqInt16# #-}
eqInt16# :: Int16# -> Int16# -> Bool
eqInt16# = noinline eqInt16#

{-# OPAQUE eqInt32# #-}
eqInt32# :: Int32# -> Int32# -> Bool
eqInt32# = noinline eqInt32#

{-# OPAQUE eqInt64# #-}
eqInt64# :: Int64# -> Int64# -> Bool
eqInt64# = noinline eqInt64#

{-# OPAQUE eqWord# #-}
eqWord# :: Word# -> Word# -> Bool
eqWord# = noinline eqWord#

{-# OPAQUE eqWord8# #-}
eqWord8# :: Word8# -> Word8# -> Bool
eqWord8# = noinline eqWord8#

{-# OPAQUE eqWord16# #-}
eqWord16# :: Word16# -> Word16# -> Bool
eqWord16# = noinline eqWord16#

{-# OPAQUE eqWord32# #-}
eqWord32# :: Word32# -> Word32# -> Bool
eqWord32# = noinline eqWord32#

{-# OPAQUE eqWord64# #-}
eqWord64# :: Word64# -> Word64# -> Bool
eqWord64# = noinline eqWord64#

-- TODO: Not sure I like this name.
-- | Convert a Haskell 'Integer' to a pantomime 'Integer'.
--
-- This function will be used to implement 'fromInteger' for pantomime
-- 'Integer', and as such will allow one to write their literals. As the
-- conversion depends on the interpretation of haskell 'Integer', we can only
-- ask a user to provide an instance for this.
{-# OPAQUE hsi2i #-}
hsi2i :: Prelude.Integer -> Integer
hsi2i = coerce

{-# OPAQUE i2hsi #-}
i2hsi :: Integer -> Prelude.Integer
i2hsi = coerce

-- | 'KnownNat' constraint using Pantomime primitive 'Integer'.
class KnownNat (n :: Nat) where
  natSing :: SNat n

instance Prelude.KnownNat n => KnownNat n where
  natSing = do
    let i = Prelude.natVal @n Proxy
    UnsafeSNat @n $ hsi2i i

instance HasDict (KnownNat n) (SNat n) where
  evidence nat = withDict @(KnownNat n) nat Dict

-- | Get the 'Integer' corresponding to the 'KnownNat' constraint.
natVal :: forall n. KnownNat n => Integer
natVal = let UnsafeSNat i = natSing @n in i

-- | Singleton natural number using Pantomime primitive 'Integer'.
newtype SNat (n :: Nat) where
  UnsafeSNat :: Integer -> SNat n

-- | A explicitly bidirectional pattern synonym relating an 'SNat' to a
-- 'KnownNat' constraint.
pattern SNat :: forall n. () => KnownNat n => SNat n
pattern SNat <- (knownNatInstance -> KnownNatInstance)
  where
    SNat = natSing
{-# COMPLETE SNat #-}

-- An internal data type that is only used for defining the SNat pattern
-- synonym.
data KnownNatInstance (n :: Nat) where
  KnownNatInstance :: KnownNat n => KnownNatInstance n

-- An internal function that is only used for defining the SNat pattern
-- synonym.
knownNatInstance :: forall n. SNat n -> KnownNatInstance n
knownNatInstance nat = withDict @(KnownNat n) nat KnownNatInstance

infixl 6 %+
(%+) :: SNat l -> SNat r -> SNat (l + r)
(%+) = coerce $ (Prelude.+) @Integer

infixl 6 %-
(%-) :: forall l r.  r <= l => SNat l -> SNat r -> SNat (l - r)
(%-) = do
  -- NOTE: The dictionary ensures it is safe to perform this subtraction. We use
  -- it here to avoid a redundant constraint warning.
  let _ = Dict @(r <= l)
  coerce $ (Prelude.-) @Integer

data SomeNat where
  SomeNat :: KnownNat n => SomeNat

someNatVal :: Integer -> Prelude.Maybe SomeNat
someNatVal i = case ilt i 0 of
  True -> Prelude.Nothing
  False -> Prelude.Just case UnsafeSNat i of
    nat@(UnsafeSNat @n _) -> withDict @(KnownNat n) nat $ SomeNat @n

-- | Helper function to get the Haskell 'KnownNat' constraint.
--
-- WARNING: Do not export this, it uses the 'Integer' internals and is only
-- intended to implement internals for other 'OPAQUE' functions.
withKnownNat
  :: forall n rep (r :: TYPE rep)
   . KnownNat n
  => (Prelude.KnownNat n => r)
  -> r
withKnownNat = do
  let UnsafeSNat (Integer i) = natSing @n
  let i' = Prelude.unsafeSNat $ Prelude.fromInteger i
  withDict @(Prelude.KnownNat n) i'

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

-- TODO: There is no real way to implement 'raise', 'tagToEnum' and 'dataToTag'
-- non-native. Maybe we could have their Haskell implementation given by a
-- plugin? For now, we can just skip it.
--
-- Another annoying thing is how we need to expose a separate 'ite' for each
-- runtime representation. Hmmm. Actually, I guess this idea would also allow
-- us to implement the other functions above no? Maybe with the exception of
-- 'tagToEnum' (for which we could probably just use unsafeCoerce on the output
-- of 'tagToEnum#'). One problem is that we would still not be able to use it
-- as an axiom for their real Haskell counterpart, as we have no way of
-- branching on which RuntimeRep is used.

-- | Tag to enumeration conversion with the intent to match 'tagToEnum#'.
--
-- WARNING: We cannot enforce that the polymorphic value is indeed an
-- enumeration, unlike the real 'tagToEnum#'. Hence, this function is incredibly
-- unsafe.
{-# OPAQUE tagToEnum #-}
tagToEnum :: forall a. BitVec PlatformWordSize -> a
tagToEnum = noinline tagToEnum

-- | Returns the index (starting at zero) of the constructor used to produce
-- the given argument.
{-# OPAQUE dataToTag #-}
dataToTag :: forall l (a :: TYPE (BoxedRep l)). a -> BitVec PlatformWordSize
dataToTag = noinline dataToTag

-- | Raise a error in the Haskell runtime.
{-# OPAQUE raise #-}
raise :: forall {l} {r} (a :: TYPE (BoxedRep l)) (b :: TYPE r). a -> b
raise = noinline raise

-- TODO: We should provide implementations for many of the common typeclasses.
-- For now, this suffices.
-- TODO: Another thing to look into is conversion between primitive types. Idk
-- if there for example is a primitive operation to convert between an boolean
-- and a single-bit bitvector.
-- | Pantomime primitive Boolean.
newtype Bool where
  Bool :: Prelude.Bool -> Bool
  deriving Hashable

instance Prelude.Eq Bool where
  (==) = convert .: iff
  (/=) = convert .: xor

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
  deriving Hashable

instance Prelude.Eq Integer where
  (==) = convert .: ieq
  (/=) = convert .: ineq

instance Prelude.Ord Integer where
  (<=) = convert .: ile
  (<) = convert .: ilt

instance Prelude.Num Integer where
  (+) = iadd
  (*) = imul
  abs = iabs
  signum x = ite (ieq 0 x) 0 $ ite (ilt 0 x) (-1) 1
  negate = ineg
  fromInteger = hsi2i

{-# OPAQUE i2bv #-}
i2bv :: forall n. KnownNat n => 1 <= n => Integer -> BitVec n
i2bv (Integer x) = withKnownNat @n $ BitVec (Prelude.fromInteger x)

{-# OPAQUE ineg #-}
ineg :: Integer -> Integer
ineg = coerce $ Prelude.negate @Prelude.Integer

{-# OPAQUE iabs #-}
iabs :: Integer -> Integer
iabs = coerce $ Prelude.abs @Prelude.Integer

{-# OPAQUE iadd #-}
iadd :: Integer -> Integer -> Integer
iadd = coerce $ (Prelude.+) @Prelude.Integer

{-# OPAQUE imul #-}
imul :: Integer -> Integer -> Integer
imul = coerce $ (Prelude.*) @Prelude.Integer

{-# OPAQUE idiv #-}
idiv :: Integer -> Integer -> Integer
idiv = coerce $ Prelude.div @Prelude.Integer

{-# OPAQUE imod #-}
imod :: Integer -> Integer -> Integer
imod = coerce $ Prelude.mod @Prelude.Integer

{-# OPAQUE ieq #-}
ieq :: Integer -> Integer -> Bool
ieq = coerce $ (Prelude.==) @Prelude.Integer

{-# OPAQUE ineq #-}
ineq :: Integer -> Integer -> Bool
ineq = coerce $ (Prelude./=) @Prelude.Integer

{-# OPAQUE ile #-}
ile :: Integer -> Integer -> Bool
ile = coerce $ (Prelude.<=) @Prelude.Integer

{-# OPAQUE ilt #-}
ilt :: Integer -> Integer -> Bool
ilt = coerce $ (Prelude.<) @Prelude.Integer

-- | Pantomime primitive bitvector.
data BitVec (n :: Nat) where
  BitVec :: (Prelude.KnownNat n, 1 <= n) => Util.BitVec n -> BitVec n

type role BitVec nominal

instance Prelude.Eq (BitVec n) where
  (==) lhs rhs = convert $ bveq lhs rhs

-- FIXME: This instance is super wrong. It uses the internal representation
-- without any opaque stuff.
instance Hashable (BitVec n) where
  hashWithSalt i (BitVec x) = hashWithSalt i x

instance (KnownNat n, 1 <= n) => Prelude.Num (BitVec n) where
  (+) = bvadd
  (*) = bvmul
  abs = Prelude.id
  signum value = ite (bveq value 0) 0 1
  fromInteger = i2bv . hsi2i
  negate = bvneg

bvunary
  :: (Prelude.KnownNat n => 1 <= n => Util.BitVec n -> Util.BitVec n)
  -> BitVec n
  -> BitVec n
bvunary f (BitVec x) = BitVec $ f x

bvbinary
  :: (Prelude.KnownNat n => 1 <= n => Util.BitVec n -> Util.BitVec n -> Util.BitVec n)
  -> BitVec n
  -> BitVec n
  -> BitVec n
bvbinary f (BitVec x) (BitVec y) = BitVec $ f x y

bvcompare
  :: (Prelude.KnownNat n => 1 <= n => Util.BitVec n -> Util.BitVec n -> Prelude.Bool)
  -> BitVec n
  -> BitVec n
  -> Bool
bvcompare f (BitVec x) (BitVec y) = case f x y of
  Prelude.True -> True
  Prelude.False -> False

signedBin
  :: forall n
   . Prelude.KnownNat n => 1 <= n
  => (IntN n -> IntN n -> IntN n)
  -> Util.BitVec n
  -> Util.BitVec n
  -> Util.BitVec n
signedBin f lhs rhs = do
  let lhs' = toSigned lhs
  let rhs' = toSigned rhs
  toUnsigned $ f lhs' rhs'

signedCmp
  :: forall n
   . Prelude.KnownNat n
  => 1 <= n
  => (IntN n -> IntN n -> Prelude.Bool)
  -> Util.BitVec n
  -> Util.BitVec n
  -> Prelude.Bool
signedCmp f lhs rhs = do
  let lhs' = toSigned lhs
  let rhs' = toSigned rhs
  f lhs' rhs'

{-# OPAQUE bv2i #-}
bv2i :: forall n. BitVec n -> Integer
bv2i (BitVec x) = Integer $ Prelude.toInteger x

{-# OPAQUE bvsize #-}
bvsize :: forall n. BitVec n -> Integer
bvsize BitVec {} = Integer $ Prelude.natVal @n Proxy

-- TODO: I guess 'bvnat' should just be called 'bvsize' and then 'bvsize' should
-- get an uglier name.
-- TODO: Somehow it makes more sense to me to return 'SNat n'. I think for this
-- one btw, we might be able to just construct it within Pantomime. I.e. then we
-- don't need the ugly 'bvsize' trick.
bvnat :: forall n. BitVec n -> Dict (KnownNat n)
bvnat bv = do
  let nat = UnsafeSNat @n $ bvsize bv
  withDict @(KnownNat n) nat Dict

{-# OPAQUE bvnot #-}
bvnot :: forall n. BitVec n -> BitVec n
bvnot = bvunary Prelude.complement

{-# OPAQUE bvneg #-}
bvneg :: forall n. BitVec n -> BitVec n
bvneg = bvunary Prelude.negate

{-# OPAQUE bvand #-}
bvand :: forall n. BitVec n -> BitVec n -> BitVec n
bvand = bvbinary (Prelude..&.)

{-# OPAQUE bvor #-}
bvor :: forall n. BitVec n -> BitVec n -> BitVec n
bvor = bvbinary (Prelude..|.)

{-# OPAQUE bvxor #-}
bvxor :: forall n. BitVec n -> BitVec n -> BitVec n
bvxor = bvbinary Prelude.xor

{-# OPAQUE bvadd #-}
bvadd :: forall n. BitVec n -> BitVec n -> BitVec n
bvadd = bvbinary (Prelude.+)

{-# OPAQUE bvmul #-}
bvmul :: forall n. BitVec n -> BitVec n -> BitVec n
bvmul = bvbinary (Prelude.*)

{-# OPAQUE bvudiv #-}
bvudiv :: forall n. BitVec n -> BitVec n -> BitVec n
bvudiv = bvbinary Prelude.div

{-# OPAQUE bvsdiv #-}
bvsdiv :: forall n. BitVec n -> BitVec n -> BitVec n
bvsdiv = bvbinary $ signedBin Prelude.div

{-# OPAQUE bvurem #-}
bvurem :: forall n. BitVec n -> BitVec n -> BitVec n
bvurem = bvbinary Prelude.rem

{-# OPAQUE bvsrem #-}
bvsrem :: forall n. BitVec n -> BitVec n -> BitVec n
bvsrem = bvbinary $ signedBin Prelude.rem

{-# OPAQUE bvshl #-}
bvshl :: forall n. BitVec n -> BitVec n -> BitVec n
bvshl = bvbinary symShift

{-# OPAQUE bvlshr #-}
bvlshr :: forall n. BitVec n -> BitVec n -> BitVec n
bvlshr = bvbinary symShiftNegated

{-# OPAQUE bvashr #-}
bvashr :: forall n. BitVec n -> BitVec n -> BitVec n
bvashr = bvbinary $ signedBin symShiftNegated

{-# OPAQUE bveq #-}
bveq :: forall n. BitVec n -> BitVec n -> Bool
bveq = bvcompare (Prelude.==)

{-# OPAQUE bvneq #-}
bvneq :: forall n. BitVec n -> BitVec n -> Bool
bvneq = bvcompare (Prelude./=)

{-# OPAQUE bvule #-}
bvule :: forall n. BitVec n -> BitVec n -> Bool
bvule = bvcompare (Prelude.<=)

{-# OPAQUE bvsle #-}
bvsle :: forall n. BitVec n -> BitVec n -> Bool
bvsle = bvcompare $ signedCmp (Prelude.<=)

{-# OPAQUE bvult #-}
bvult :: forall n. BitVec n -> BitVec n -> Bool
bvult = bvcompare (Prelude.<)

{-# OPAQUE bvslt #-}
bvslt :: forall n. BitVec n -> BitVec n -> Bool
bvslt = bvcompare $ signedCmp (Prelude.<)

{-# OPAQUE bvconcat #-}
bvconcat :: forall l r. BitVec l -> BitVec r -> BitVec (l + r)
bvconcat (BitVec lhs) (BitVec rhs) = runIdentity do
  SomeNat' @sum <- pure $ typeAdd @l @r
  -- SAFETY: Sum of two positives is also positive.
  Dict <- pure $ unsafeAxiom @(1 <= sum)
  pure $ BitVec (sizedBVConcat lhs rhs)

{-# OPAQUE bvzext #-}
bvzext :: forall l r. KnownNat r => l <= r => BitVec l -> BitVec r
-- SAFETY: Follows from transitivity on the constraints as BitVec internally
-- carries '1 <= l'.
bvzext (BitVec x) = withKnownNat @r case unsafeAxiom @(1 <= r) of
  Dict -> BitVec $ sizedBVZext Proxy x

{-# OPAQUE bvsext #-}
bvsext :: forall l r. KnownNat r => l <= r => BitVec l -> BitVec r
-- SAFETY: Follows from transitivity on the constraints as BitVec internally
-- carries '1 <= l'.
bvsext (BitVec x) = withKnownNat @r case unsafeAxiom @(1 <= r) of
  Dict -> BitVec $ sizedBVSext Proxy x

{-# OPAQUE bvselect #-}
bvselect
  :: forall idx width n
   . KnownNat idx
  => KnownNat width
  => 1 <= width
  => idx + width <= n
  => BitVec n
  -> BitVec width
bvselect (BitVec x) = withKnownNat @idx $ withKnownNat @width do
  BitVec $ sizedBVSelect (Proxy @idx) (Proxy @width) x

bvresize
  :: forall l r
   . KnownNat r
  => 1 <= r
  => (l <= r => BitVec l -> BitVec r)
  -> BitVec l
  -> BitVec r
bvresize f x = do
  let l = bvsize x
  let r = natVal @r
  case Prelude.compare l r of
    LT | Dict <- unsafeAxiom @(l <= r) -> f x
    EQ | Dict <- unsafeEq @l @r -> x
    GT | Dict <- unsafeAxiom @(r <= l) -> bvselect @0 @r x

bvzresize
  :: forall l r
   . KnownNat r
  => 1 <= r
  => BitVec l
  -> BitVec r
bvzresize = bvresize bvzext

bvsresize
  :: forall l r
   . KnownNat r
  => 1 <= r
  => BitVec l
  -> BitVec r
bvsresize = bvresize bvsext

newtype Array (k :: Type) (v :: Type) where
  Array :: Grisette.Array k v -> Array k v
  -- FIXME: The derive on these is super wrong. Any usage of it will break...
  -- Check out 'Primitive' in order to see why.
  deriving (Prelude.Eq, Hashable)

-- TODO: I think we kind of need this? I'm not sure...
type role Array nominal nominal

-- TODO: Maybe it makes more sense to let 'Primitive' be carried inside of
-- 'Array'. I think this reflects a bit better the array primitive under the
-- hood?
{-# OPAQUE aconst #-}
aconst :: forall k v. Primitive k => Primitive v => v -> Array k v
aconst = coerce $ Grisette.const @k @v

{-# OPAQUE aselect #-}
aselect :: forall k v. Primitive k => Primitive v => Array k v -> k -> v
aselect = coerce $ Grisette.select @k @v

{-# OPAQUE astore #-}
astore
  :: forall k v
   . Primitive k
  => Primitive v
  => Array k v
  -> k
  -> v
  -> Array k v
astore = coerce $ Grisette.store @k @v

{-# OPAQUE aeq #-}
aeq
  :: forall k v
   . Primitive k
  => Primitive v
  => Array k v
  -> Array k v
  -> Bool
aeq = coerce $ (Prelude.==) @(Grisette.Array k v)
