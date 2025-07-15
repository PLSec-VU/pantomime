{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Pantomime.WordSize
  ( KnownWordSize
  , WordBits

  , IntPW (..)
  , unIntPW

  , WordPW (..)
  , unWordPW

  , BitSize
  , EvalMode
  , Shift (..)
  ) where

import Grisette
  ( SymOrd (..)
  , SymEq
  , SymShift (..)
  , LogicalOp (..)
  , SymFromIntegral (..)
  , SignConversion (..)
  , EvalSym
  , Mergeable
  , SimpleMergeable (..)
  , GenSym (..)
  , GenSymSimple (..)
  , SExpr (..)
  , BitCast (..)
  , ToCon (..)
  , ToSym (..)
  , ConRep (..)
  , SymInteger
  , Identifier
  , withMetadata
  , genSymSimple
  )

import GHC.TypeLits (KnownNat, Nat, natVal)
import GHC.Platform

import Data.Bits (Bits)

import Grisette.Unified (DecideEvalMode (..), EvalModeTag (..), withMode)

import Pantomime.Grisette.BitVector
import Data.Data (Proxy(..))

-- TODO: Perhaps KnownPW is better? Idk, I dislike the current name.
-- | Constraint to ensure that the WordBits are non-zero.
--
-- Note that technically we shouldn't really need this, as WordBits can never be
-- zero. Still, Haskell cannot prove this and as such we tag around this
-- typeclass constraint.
type KnownWordSize ws = KnownNat (WordBits ws)

-- | Type family to get a type natural corresponding to the number of bits in
-- the given platform word size.
type WordBits :: PlatformWordSize -> Nat
type family WordBits ws = n | n -> ws where
  WordBits PW4 = 32
  WordBits PW8 = 64

-- | Wrapper to allow alternative typeclass instances for word-sized ints.
newtype IntPW mode ws where
  IntPW :: IntN mode (WordBits ws) -> IntPW mode ws

unIntPW :: IntPW mode ws -> IntN mode (WordBits ws)
unIntPW (IntPW value) = value

deriving via IntN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => Show (IntPW mode ws)

deriving via IntN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => Num (IntPW mode ws)

deriving via IntN C (WordBits ws)
  instance KnownWordSize ws
  => Enum (IntPW C ws)

deriving via IntN C (WordBits ws)
  instance KnownWordSize ws
  => Real (IntPW C ws)

deriving via IntN C (WordBits ws)
  instance KnownWordSize ws
  => Integral (IntPW C ws)

deriving via IntN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => Eq (IntPW mode ws)

deriving via IntN C (WordBits ws)
  instance KnownWordSize ws
  => Ord (IntPW C ws)

deriving via IntN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => Bits (IntPW mode ws)

deriving via IntN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => SymOrd (IntPW mode ws)

deriving via IntN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => SymEq (IntPW mode ws)

deriving via IntN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => SymShift (IntPW mode ws)

deriving via IntN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws, KnownNat n)
  => SymFromIntegral (IntN mode n) (IntPW mode ws)

deriving via IntN mode n
  instance (DecideEvalMode mode, KnownWordSize ws, KnownNat n)
  => SymFromIntegral (IntPW mode ws) (IntN mode n)

deriving via IntN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws, KnownNat n)
  => SymFromIntegral (WordN mode n) (IntPW mode ws)

deriving via IntN mode n
  instance (DecideEvalMode mode, KnownWordSize ws, KnownNat n)
  => SymFromIntegral (WordPW mode ws) (IntN mode n)

deriving via IntN mode (WordBits ws')
  instance (DecideEvalMode mode, KnownWordSize ws, KnownWordSize ws')
  => SymFromIntegral (IntPW mode ws) (IntPW mode ws')

deriving via IntN mode (WordBits ws')
  instance (DecideEvalMode mode, KnownWordSize ws, KnownWordSize ws')
  => SymFromIntegral (WordPW mode ws) (IntPW mode ws')

deriving via IntN S (WordBits ws)
  instance KnownWordSize ws
  => SymFromIntegral SymInteger (IntPW S ws)

deriving via SymInteger
  instance KnownWordSize ws
  => SymFromIntegral (IntPW S ws) SymInteger

deriving via IntN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => EvalSym (IntPW mode ws)

deriving via IntN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => Mergeable (IntPW mode ws)

deriving via IntN S (WordBits ws)
  instance KnownWordSize ws
  => SimpleMergeable (IntPW S ws)

instance (DecideEvalMode mode, KnownWordSize ws) => ToCon (IntPW mode ws) (IntPW C ws) where
  toCon = fmap IntPW . toCon . unIntPW

instance (DecideEvalMode mode, KnownWordSize ws) => ToSym (IntPW mode ws) (IntPW S ws) where
  toSym = IntPW . toSym . unIntPW

instance (DecideEvalMode mode, KnownWordSize ws) => GenSym (IntPW mode ws) (IntPW mode ws)

instance KnownWordSize ws => GenSym () (IntPW S ws)

instance GenSymSimple (IntPW mode ws) (IntPW mode ws) where
  simpleFresh = pure

instance KnownWordSize ws => GenSymSimple () (IntPW S ws) where
  simpleFresh = fmap IntPW . simpleFresh

instance ConRep (IntPW S ws) where
  type ConType (IntPW S ws) = IntPW C ws

-- | Wrapper to allow alternative typeclass instances for word-sized words.
newtype WordPW mode ws where
  WordPW :: WordN mode (WordBits ws) -> WordPW mode ws

unWordPW :: WordPW mode ws -> WordN mode (WordBits ws)
unWordPW (WordPW value) = value

deriving via WordN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => Show (WordPW mode ws)

deriving via WordN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => Num (WordPW mode ws)

deriving via WordN C (WordBits ws)
  instance KnownWordSize ws
  => Enum (WordPW C ws)

deriving via WordN C (WordBits ws)
  instance KnownWordSize ws
  => Real (WordPW C ws)

deriving via WordN C (WordBits ws)
  instance KnownWordSize ws
  => Integral (WordPW C ws)

deriving via WordN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => Eq (WordPW mode ws)

deriving via WordN C (WordBits ws)
  instance KnownWordSize ws
  => Ord (WordPW C ws)

deriving via WordN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => Bits (WordPW mode ws)

deriving via WordN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => SymOrd (WordPW mode ws)

deriving via WordN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => SymEq (WordPW mode ws)

deriving via WordN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => SymShift (WordPW mode ws)

deriving via WordN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws, KnownNat n)
  => SymFromIntegral (IntN mode n) (WordPW mode ws)

deriving via WordN mode n
  instance (DecideEvalMode mode, KnownWordSize ws, KnownNat n)
  => SymFromIntegral (IntPW mode ws) (WordN mode n)

deriving via WordN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws, KnownNat n)
  => SymFromIntegral (WordN mode n) (WordPW mode ws)

deriving via WordN mode n
  instance (DecideEvalMode mode, KnownWordSize ws, KnownNat n)
  => SymFromIntegral (WordPW mode ws) (WordN mode n)

deriving via WordN mode (WordBits ws')
  instance (DecideEvalMode mode, KnownWordSize ws, KnownWordSize ws')
  => SymFromIntegral (WordPW mode ws) (WordPW mode ws')

deriving via WordN mode (WordBits ws')
  instance (DecideEvalMode mode, KnownWordSize ws, KnownWordSize ws')
  => SymFromIntegral (IntPW mode ws) (WordPW mode ws')

deriving via WordN S (WordBits ws)
  instance KnownWordSize ws
  => SymFromIntegral SymInteger (WordPW S ws)

deriving via SymInteger
  instance KnownWordSize ws
  => SymFromIntegral (WordPW S ws) SymInteger

deriving via WordN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => EvalSym (WordPW mode ws)

deriving via WordN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => Mergeable (WordPW mode ws)

deriving via WordN S (WordBits ws)
  instance KnownWordSize ws
  => SimpleMergeable (WordPW S ws)

instance (DecideEvalMode mode, KnownWordSize ws) => ToCon (WordPW mode ws) (WordPW C ws) where
  toCon = fmap WordPW . toCon . unWordPW

instance (DecideEvalMode mode, KnownWordSize ws) => ToSym (WordPW mode ws) (WordPW S ws) where
  toSym = WordPW . toSym . unWordPW

instance (DecideEvalMode mode, KnownWordSize ws) => GenSym (WordPW mode ws) (WordPW mode ws)

instance KnownWordSize ws => GenSym () (WordPW S ws)

instance GenSymSimple (WordPW mode ws) (WordPW mode ws) where
  simpleFresh = pure

instance KnownWordSize ws => GenSymSimple () (WordPW S ws) where
  simpleFresh = fmap WordPW . simpleFresh

instance (DecideEvalMode mode, KnownWordSize ws)
  => SignConversion (WordPW mode ws) (IntPW mode ws) where
  toSigned = IntPW . toSigned . unWordPW
  toUnsigned = WordPW . toUnsigned . unIntPW

instance ConRep (WordPW S ws) where
  type ConType (WordPW S ws) = WordPW C ws

-- | Type family to statically lookup the size of a bitvector.
--
-- This may be used to determine the size of bitvectors whose size does not
-- necessarily depend on a type-level natural.
type family BitSize a :: Nat

type instance BitSize (IntN mode n) = n
type instance BitSize (WordN mode n) = n
type instance BitSize (IntPW mode ws) = WordBits ws
type instance BitSize (WordPW mode ws) = WordBits ws

-- | Type family to look up the evaluation mode of a type.
-- TODO: This type family should go somewhere in the Pantomime.Grisette.X
-- corner. Same for the BitSize type family btw!
type family EvalMode a :: EvalModeTag

type instance EvalMode (IntN mode n) = mode
type instance EvalMode (WordN mode n) = mode
type instance EvalMode (IntPW mode ws) = mode
type instance EvalMode (WordPW mode ws) = mode

-- | Haskell-like shift functions.
class Shift a where
  -- | Shift right arithmetic.
  shiftRA :: KnownWordSize ws => a -> IntPW (EvalMode a) ws -> a
  -- | Shift right logical.
  shiftRL :: KnownWordSize ws => a -> IntPW (EvalMode a) ws -> a
  -- | Shift left.
  shiftL :: KnownWordSize ws => a -> IntPW (EvalMode a) ws -> a

instance (DecideEvalMode mode, KnownNat n) => Shift (IntN mode n) where
  shiftRA = shiftRA'
  shiftRL value idx = bitCast $ shiftRL' @_ @n (bitCast value) idx
  shiftL = shiftL'

instance (DecideEvalMode mode, KnownNat n) => Shift (WordN mode n) where
  shiftRA value idx = bitCast $ shiftRA' @_ @n (bitCast value) idx
  shiftRL = shiftRL'
  shiftL value idx = bitCast $ shiftL' @_ @n (bitCast value) idx

deriving via IntN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => Shift (IntPW mode ws)

deriving via WordN mode (WordBits ws)
  instance (DecideEvalMode mode, KnownWordSize ws)
  => Shift (WordPW mode ws)

-- | Shift right arithmetic helper.
shiftRA'
  :: forall mode n ws
   . DecideEvalMode mode
  => KnownNat n
  => KnownWordSize ws
  => IntN mode n
  -> IntPW mode ws
  -> IntN mode n
shiftRA' = do
  let ident = withMetadata "shiftRA" (Atom "Pantomime.UB")
  shift' ident symShiftNegated

-- | Shift right logical helper.
shiftRL'
  :: forall mode n ws
   . DecideEvalMode mode
  => KnownNat n
  => KnownWordSize ws
  => WordN mode n
  -> IntPW mode ws
  -> WordN mode n
shiftRL' = do
  let ident = withMetadata "shiftRL" (Atom "Pantomime.UB")
  shift' ident symShiftNegated

-- | Shift left helper.
shiftL'
  :: forall mode n ws
   . DecideEvalMode mode
  => KnownNat n
  => KnownWordSize ws
  => IntN mode n
  -> IntPW mode ws
  -> IntN mode n
shiftL' = do
  -- TODO: How do we ensure that this uninterpreted function is truly
  -- unique? Perhaps the best we can do is put all constant values in one
  -- place. The alternative is perhaps to use 'withLocation' from pantomime.
  -- I guess it is also still technically something that can be recreated.
  -- Same problem for the other shifts btw.
  let ident = withMetadata "shiftL" (Atom "Pantomime.UB")
  shift' ident symShift

-- | Generalised Haskell shift operation.
--
-- Haskell shifts have undefined behaviour for indices outside of the range
-- '0 <= idx < n'.  In the symbolic instance, we model undefined behaviour via
-- an uninterpreted function call. The concrete shift will apply Grisette shift
-- semantics; any behaviour will do as its result is undefined.
shift'
  :: forall mode bv ws
   . DecideEvalMode mode
  => KnownWordSize ws
  => KnownNat (BitSize bv)
  => SymFromIntegral (IntPW mode ws) bv
  => (mode ~ S => GenSymSimple () bv)
  => (mode ~ S => SimpleMergeable bv)
  => Identifier
  -- ^ Identifier for uninterpreted function when shift is out of bounds. This
  -- is to model undefined behaviour.
  -> (bv -> bv -> bv)
  -- ^ The shift function.
  -> bv
  -- ^ Bitvector to shift.
  -> IntPW mode ws
  -- ^ Index; how much to shift by.
  -> bv
shift' ident f value idx = do
  -- The normal result of the computation
  let idx' = symFromIntegral idx
  let result = f value idx'

  -- An implementation is allowed to do whatever for undefined behaviour.
  -- As such, for concrete evaluation we just return whatever Grisette
  -- computes for out-of-bounds shifts.
  withMode @mode result do
    -- The bit-size of platform words.
    let size = fromInteger $ natVal (Proxy @(BitSize bv))

    -- The bounds within which a shift is defined.
    let isBound = 0 .<= idx .&& idx .< size

    -- In the symbolic instance, we model undefined behaviour via an
    -- uninterpreted function.
    let ub = genSymSimple () ident

    -- The final result.
    mrgIte isBound result ub
