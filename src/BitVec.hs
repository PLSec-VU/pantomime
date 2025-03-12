{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

module BitVec
  ( symShiftRA
  , symShiftRL
  , symShiftL
  , sizedBVResize
  ) where

import Unsafe.Coerce (unsafeCoerce)

import Data.Data (type (:~:) (..), Proxy (..))
import Data.Type.Ord (Compare)

import GHC.TypeLits (OrderingI (..), cmpNat)

import SymUtil

import Grisette

-- | Symbolic Shift Right Arithmetic.
--
-- This will use a conversion into a signed bitvector, as the symbolic executor
-- does not distinguish between arithmetic and logical shift per type.
symShiftRA
  :: forall bv n i
   . SymFromIntegral (SymIntN n) (bv n)
  => SymFromIntegral (bv n) (SymIntN n)
  => KnownPos n
  => KnownPos i
  => bv n
  -> SymIntN i
  -> bv n
symShiftRA val idx = do
  let idx' = sizedBVResize idx :: SymIntN n
  let idx'' = symFromIntegral idx'

  let val' = symFromIntegral val :: SymIntN n
  -- TODO: Same thing as with symShiftL (i.e. non-total function)
  let result = symShiftNegated val' idx''
  symFromIntegral result

-- | Symbolic Shift Right Logical.
--
-- This will use a conversion into a signed bitvector, as the symbolic executor
-- does not distinguish between arithmetic and logical shift per type.
symShiftRL
  :: forall bv n i
   . SymFromIntegral (SymWordN n) (bv n)
  => SymFromIntegral (bv n) (SymWordN n)
  => KnownPos n
  => KnownPos i
  => bv n
  -> SymIntN i
  -> bv n
symShiftRL val idx = do
  let idx' = sizedBVResize idx :: SymIntN n
  let idx'' = symFromIntegral idx'

  let val' = symFromIntegral val :: SymWordN n
  -- TODO: Same thing as with symShiftL (i.e. non-total function)
  let result = symShiftNegated val' idx''
  symFromIntegral result

-- | Symbolic Shift Left
--
-- Symbolic shifts in Haskell all use the platform-sized int for the index (i.e.
-- the amount to shift by). This function performs the necessary conversions in
-- order to be compatible with the symbolic shift.
symShiftL
  :: forall bv n i
   . SymFromIntegral (SymIntN n) (bv n)
  => SymShift (bv n)
  => KnownPos n
  => KnownPos i
  => bv n
  -> SymIntN i
  -> bv n
symShiftL val idx = do
  let idx' = sizedBVResize idx :: SymIntN n
  let idx'' = symFromIntegral idx'
  -- TODO: Haskell doesn't really define what to do with the shift if the index
  -- is larger than the word size. It is considered unsafe. We should do
  -- something with this? Not sure what exactly that would be though... How
  -- would we ever model UB? Just for comparison btw, the safe version of the
  -- primitive shifts just masks the value to 0 if it excedes the size. Other
  -- implementations (like Word8) actually throw an error...
  --
  -- In any case, they all do something to wrap the UB into non-UB. There is
  -- no direct way to model the UB I guess... Maybe it is okay to assume that
  -- only safe uses exist? I.e. with non-UB behaviour at the top level. Then it
  -- doens't matter what we do for those cases anyway, as they're wrapped into
  -- something that is always defined.
  --
  -- One thing we do need to account for is failure. Currently we do not track
  -- failure of functions anywhere, but I guess we techinically should?
  --
  -- Now that I think about it btw, I don't think a shift will ever actually
  -- occur in hardware? Maybe I've been caring slightly too much about them?
  symShift val idx''

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
sizedBVResize = case cmpNat (Proxy @l) (Proxy @r) of
  LTI -> sizedBVExt $ Proxy @r
  EQI -> id
  -- SAFETY: The unsafe coerce is just to have 'r <= l' as Haskell cannot figure
  -- this out given the 'l >= r' that is already in context. Theoretically we
  -- should be able to do this without unsafeCoerce, but I'm not sure how.
  -- I'm not keen on importing the type level nat plugin for just one function.
  GTI -> case unsafeCoerce Refl :: (Compare r l :~: 'LT) of
    Refl -> sizedBVSelect (Proxy @0) (Proxy @r)

