{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UndecidableInstances #-}

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
  ( Embeddable
  , embed

  -- | Typeclass to differntiate primitive types.
  , Primitive

  -- | Built-in literal conversion functions.
  --
  -- WARNING: These functions should not be called directly. Their purpose is
  -- to receive an interpretation such that the symbolic engine knows how to
  -- construct these literals from GHC Core.
  , toInt#
  , toInt8#
  , toInt16#
  , toInt32#
  , toInt64#

  , ite
  , tagToEnum
  , dataToTag

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

  , Integer
  -- , ineg
  -- , iabs
  , iadd
  -- , imul
  -- , idiv
  -- , imod
  -- , ieq
  -- , ineq
  -- , ile
  -- , ilt

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
  , bvselect

  , Array
  , aconst
  , aselect
  , astore
  ) where

-- import Data.Composition ((.:))
-- import Data.Bits qualified as Prelude
import Data.Coerce (coerce)
-- import Pantomime.Util (KnownPos)
-- import Pantomime.Util qualified as Util
-- import GHC.TypeNats (Nat, type (+), type (<=), type (-))
import GHC.TypeNats (Nat, KnownNat, type (+), type (<=))
import Prelude qualified
import Prelude (($))
import GHC.Base
  ( TYPE
  , RuntimeRep (BoxedRep)
  , Int#
  , Int8#
  , Int16#
  , Int32#
  , Int64#, Constraint, Type
  )
import GHC.TypeLits (TypeError, ErrorMessage (..))

class Embeddable (a :: TYPE r1) (b :: TYPE r2)

embed
  :: forall {r1} {r2} (a :: TYPE r1) (b :: TYPE r2) 
   . Embeddable a b
  => a
  -> b
embed = embed

type family Primitive a :: Constraint where
  Primitive Bool = ()
  Primitive Integer = ()
  Primitive (BitVec n) = 1 <= n
  Primitive (Array k v) = (Primitive k, Primitive v)
  Primitive x = TypeError ('Text "'" :<>: ShowType x :<>: 'Text "' is not a primitive type")

-- TODO: For now, we'll just have the platform sized int as 64-bit. Not sure how
-- we would handle this correctly? Maybe with a pragma?
-- | Literal construction function for built-in Haskell 'Int#' literal. Note
-- that
{-# OPAQUE toInt# #-}
toInt# :: BitVec 64 -> Int#
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

-- TODO: There is no real way to implement 'ite', 'tagToEnum' and 'dataToTag'
-- non-native. Maybe we could have their Haskell implementation given by a
-- plugin? For now, we can just skip it.

-- | Primitive if-then-else construct.
{-# OPAQUE ite #-}
ite :: forall l (a :: TYPE (BoxedRep l)). Bool -> a -> a -> a
ite = ite

-- | Tag to enumeration conversion with the intent to match 'tagToEnum#'.
--
-- WARNING: We cannot enforce that the polymorphic value is indeed an
-- enumeration, unlike the real 'tagToEnum#'. Hence, this function is incredibly
-- unsafe.
{-# OPAQUE tagToEnum #-}
tagToEnum :: forall a. BitVec 64 -> a
tagToEnum = tagToEnum

-- | Returns the index (starting at zero) of the constructor used to produce
-- the given argument.
{-# OPAQUE dataToTag #-}
dataToTag :: forall l (a :: TYPE (BoxedRep l)). a -> BitVec 64
dataToTag = dataToTag

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

{-# OPAQUE iadd #-}
iadd :: Integer -> Integer -> Integer
iadd = coerce $ (Prelude.+) @Prelude.Integer

-- , ineg
-- , iabs
-- , iadd
-- , imul
-- , idiv
-- , imod
-- , ieq
-- , ineq
-- , ile
-- , ilt

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
