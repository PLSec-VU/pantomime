{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableSuperClasses #-}
-- {-# LANGUAGE UndecidableInstances #-}

module Pantomime.WordSize
  ( KnownWordSize
  , WordBits
  , KnownPos
  , KnownBitSize (..)

  , SymInt (..)
  , SymWord (..)

  , symShiftRA
  , symShiftRL
  , symShiftL
  , sizedBVResize
  ) where

import Grisette
  ( SymIntN
  , SymWordN
  , SymOrd
  , SymEq
  , SymShift (..)
  , SymFromIntegral (..)
  , SizedBV (..)
  , SignConversion (..)
  , unsafeAxiom
  )

import GHC.TypeLits (KnownNat, type (<=), Nat, OrderingI (..), cmpNat)
import GHC.Platform

import Data.Bits (Bits)
import Data.Data (type (:~:) (..), Proxy (..))
import Data.Type.Ord (Compare)

-- import Grisette

-- | Constraint to ensure that the WordBits are non-zero.
--
-- Note that technically we shouldn't really need this, as WordBits can never be
-- zero. Still, Haskell cannot prove this and as such we tag around this
-- typeclass constraint.
type KnownWordSize ws = KnownPos (WordBits ws)

-- | Type family to get a type natural corresponding to the number of bits in
-- the given platform word size.
type WordBits :: PlatformWordSize -> Nat
type family WordBits ws = n | n -> ws where
  WordBits PW4 = 32
  WordBits PW8 = 64

-- | Constraint required by most bit-operations on grisette bitvectors.
type KnownPos n = (KnownNat n, 1 <= n)

-- | Wrapper to allow alternative typeclass instances for word-sized ints.
--
-- Note that in order to solve for this word-sized int, one needs to unwrap it.
-- This is due to the functional dependency between symbolic and non-symbolic
-- values in Grisette.
-- TODO: We should really adjust SymInt to get a EvalModeTag which makes it
-- select either the concrete or symbolic int (with of course the correct word
-- size). I guess we don't need to create a new type family here, as we can just
-- us GetIntN (and GetWordN respectively for the word size stuff). Maybe the
-- new name for this would need to be PlatformInt (and PlatformWord). I'll have
-- to think about it...
newtype SymInt ws where
  SymInt :: { unSymInt :: SymIntN (WordBits ws) } -> SymInt ws

deriving via SymIntN (WordBits ws)
  instance KnownWordSize ws
  => Num (SymInt ws)

deriving via SymIntN (WordBits ws)
  instance KnownWordSize ws
  => Eq (SymInt ws)

deriving via SymIntN (WordBits ws)
  instance KnownWordSize ws
  => Bits (SymInt ws)

deriving via SymIntN (WordBits ws)
  instance KnownWordSize ws
  => SymOrd (SymInt ws)

deriving via SymIntN (WordBits ws)
  instance KnownWordSize ws
  => SymEq (SymInt ws)

deriving via SymIntN (WordBits ws)
  instance KnownWordSize ws
  => SymShift (SymInt ws)

deriving via SymIntN (WordBits ws)
  instance (KnownWordSize ws, KnownPos n)
  => SymFromIntegral (SymIntN n) (SymInt ws)

deriving via SymIntN (WordBits ws)
  instance (KnownWordSize ws, KnownPos n)
  => SymFromIntegral (SymWordN n) (SymInt ws)

instance (KnownWordSize ws, KnownPos n)
  => SymFromIntegral (SymInt ws) (SymIntN n) where
  symFromIntegral = symFromIntegral . unSymInt

instance (KnownWordSize ws, KnownPos n)
  => SymFromIntegral (SymInt ws) (SymWordN n) where
  symFromIntegral = symFromIntegral . unSymInt

deriving via SymIntN (WordBits ws)
  instance KnownWordSize ws
  => SymFromIntegral (SymWord ws) (SymInt ws)

deriving via SymIntN (WordBits ws)
  instance KnownWordSize ws
  => SymFromIntegral (SymInt ws) (SymInt ws)

-- | Wrapper to allow alternative typeclass instances for word-sized word.
--
-- Note that in order to solve for this word-sized word, one needs to unwrap it.
-- This is due to the functional dependency between symbolic and non-symbolic
-- values in Grisette.
newtype SymWord ws where
  SymWord :: { unSymWord :: SymWordN (WordBits ws) } -> SymWord ws

deriving via SymWordN (WordBits ws)
  instance KnownWordSize ws
  => Num (SymWord ws)

deriving via SymWordN (WordBits ws)
  instance KnownWordSize ws
  => Eq (SymWord ws)

deriving via SymWordN (WordBits ws)
  instance KnownWordSize ws
  => Bits (SymWord ws)

deriving via SymWordN (WordBits ws)
  instance KnownWordSize ws
  => SymOrd (SymWord ws)

deriving via SymWordN (WordBits ws)
  instance KnownWordSize ws
  => SymEq (SymWord ws)

deriving via SymWordN (WordBits ws)
  instance KnownWordSize ws
  => SymShift (SymWord ws)

deriving via SymWordN (WordBits ws)
  instance (KnownWordSize ws, KnownPos n)
  => SymFromIntegral (SymIntN n) (SymWord ws)

deriving via SymWordN (WordBits ws)
  instance (KnownWordSize ws, KnownPos n)
  => SymFromIntegral (SymWordN n) (SymWord ws)

instance (KnownWordSize ws, KnownPos n)
  => SymFromIntegral (SymWord ws) (SymIntN n) where
  symFromIntegral = symFromIntegral . unSymWord

instance (KnownWordSize ws, KnownPos n)
  => SymFromIntegral (SymWord ws) (SymWordN n) where
  symFromIntegral = symFromIntegral . unSymWord

deriving via SymWordN (WordBits ws)
  instance KnownWordSize ws
  => SymFromIntegral (SymInt ws) (SymWord ws)

deriving via SymWordN (WordBits ws)
  instance KnownWordSize ws
  => SymFromIntegral (SymWord ws) (SymWord ws)

instance KnownWordSize ws => SignConversion (SymWord ws) (SymInt ws) where
  toSigned = SymInt . toSigned . unSymWord
  toUnsigned = SymWord . toUnsigned . unSymInt

-- | Class to statically lookup the size of a bitvector.
--
-- This may be used to add constraints on bitvector conversion, without
-- necessarily requiring the size to be determined by a type natural as
-- argument.
class KnownPos (BitSize bv) => KnownBitSize bv where
  type BitSize bv :: Nat

instance KnownPos n => KnownBitSize (SymIntN n) where
  type BitSize (SymIntN n) = n

instance KnownPos n => KnownBitSize (SymWordN n) where
  type BitSize (SymWordN n) = n

instance KnownWordSize ws => KnownBitSize (SymWord ws) where
  type BitSize (SymWord ws) = WordBits ws

instance KnownWordSize ws => KnownBitSize (SymInt ws) where
  type BitSize (SymInt ws) = WordBits ws

-- | Symbolic Shift Right Arithmetic.
--
-- This will use a conversion into a signed bitvector, as the symbolic executor
-- does not distinguish between arithmetic and logical shift per type.
symShiftRA
  :: forall bv ws
   . KnownBitSize bv
  => SymFromIntegral bv (SymIntN (BitSize bv))
  => SymFromIntegral (SymIntN (BitSize bv)) bv
  => KnownWordSize ws
  => bv
  -> SymInt ws
  -> bv
symShiftRA val (SymInt idx) = do
  let idx' = symFromIntegral idx

  let val' = symFromIntegral val :: SymIntN (BitSize bv)
  -- TODO: Same thing as with 'symShiftL' (i.e. non-total function)
  let result = symShiftNegated val' idx'
  symFromIntegral result

-- | Symbolic Shift Right Logical.
--
-- This will use a conversion into a signed bitvector, as the symbolic executor
-- does not distinguish between arithmetic and logical shift per type.
symShiftRL
  :: forall bv ws
   . KnownBitSize bv
  => SymFromIntegral bv (SymWordN (BitSize bv))
  => SymFromIntegral (SymWordN (BitSize bv)) bv
  => KnownWordSize ws
  => bv
  -> SymInt ws
  -> bv
symShiftRL val (SymInt idx) = do
  let idx' = symFromIntegral idx

  let val' = symFromIntegral val :: SymWordN (BitSize bv)
  -- TODO: Same thing as with 'symShiftL' (i.e. non-total function)
  let result = symShiftNegated val' idx'
  symFromIntegral result

-- | Symbolic Shift Left
--
-- Symbolic shifts in Haskell all use the platform-sized int for the index (i.e.
-- the amount to shift by). This function performs the necessary conversions in
-- order to be compatible with the symbolic shift.
symShiftL
  :: forall bv ws
   . SymFromIntegral (SymInt ws) bv
  => SymShift bv
  => bv
  -> SymInt ws
  -> bv
symShiftL val idx = do
  -- TODO: Haskell doesn't really define what to do with the shift if the index
  -- is larger than the word size. It is considered unsafe/undefined behaviour.
  -- We should model this as a special runtime value "UndefinedBehaviour".
  -- Similar to how "Invalid" allows us to declare unreachable states, UB would
  -- allow us to show that we cannot conclude the outcome for a particular
  -- range of values. Comparing againt UB is always considered non-equal
  -- (and maybe should throw a warning).
  --
  -- Alternatively, we could create a fresh symbolic value for anything that is
  -- UB. The benefit of the other approach would be that we can know whether
  -- something is unconstraint due to UB. It might be a bit harder to go back
  -- to non-UB though.
  --
  -- Any safe usage of UB would mean that it is unreachable. An example would be
  -- masking all bits to zero when we shift larger than the word size. We should
  -- add something like this! In any case, having UB is bad as our symbolic
  -- execute may or may not find terms to be equal according to its own
  -- semantic. This semantic may very well not match what the machine actually
  -- does.
  --
  -- We should implement this sometime. We probably need to change the interface
  -- on this to use RuntimeValue instead. Don't forget that the same applies to
  -- both right shift operations. We can also use this for other UB, if there
  -- exists any.
  symShift val $ symFromIntegral idx

-- | Resize the given bitvector.
--
-- Whether the bitvector is sign extended or not depends on its implementation
-- of 'sizedBVExt'.
sizedBVResize
  :: forall bv l r
   . SizedBV bv
  => KnownPos l
  => KnownPos r
  => bv l
  -> bv r
sizedBVResize = case cmpNat @l @r Proxy Proxy of
  LTI -> sizedBVExt $ Proxy @r
  EQI -> id
  -- SAFETY: The unsafe coerce is just to have 'r <= l' as Haskell cannot figure
  -- this out given the 'l >= r' that is already in context. Theoretically we
  -- should be able to do this without unsafeCoerce, but I'm not sure how.
  -- I'm not keen on importing the type level nat plugin for just one function.
  GTI -> case unsafeAxiom @(Compare r l) @LT  of
    Refl -> sizedBVSelect (Proxy @0) (Proxy @r)
