{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Symbolic.Sized.IntN
  ( IntN' (..)
  ) where

import GHC.TypeNats (type (<=), Natural, KnownNat, natVal)

import Grisette hiding (fill)
import Grisette.Unified (EvalModeTag (..), GetIntN)
import qualified Grisette.Unified as Unified

import Data.Bits (Bits (..), FiniteBits (..))
import Data.Data (Proxy(..))

import Symbolic.Dict (withSize)

data IntN' (mode :: EvalModeTag) (n :: Natural) where
  IntZ :: IntN' mode 0
  IntP :: 1 <= n => GetIntN mode n -> IntN' mode n

binary
  :: forall mode n
   . (1 <= n => GetIntN mode n -> GetIntN mode n -> GetIntN mode n)
  -> IntN' mode n
  -> IntN' mode n
  -> IntN' mode n
binary op = curry $ \case
  (IntZ, IntZ) -> IntZ
  (IntP lhs, IntP rhs) -> IntP $ op lhs rhs

unary
  :: forall mode n
   . (1 <= n => GetIntN mode n -> GetIntN mode n)
  -> IntN' mode n
  -> IntN' mode n
unary op = \case
  IntZ -> IntZ
  IntP value -> IntP $ op value

withSize' :: forall n mode. KnownNat n => (1 <= n => GetIntN mode n) -> IntN' mode n
withSize' value = withSize @n IntZ (IntP value)

instance (Unified.DecideEvalMode mode, KnownNat n) => Eq (IntN' mode n) where
  (==) = curry $ \case
    (IntZ, IntZ) -> true
    (IntP lhs, IntP rhs) -> do
      let op = Unified.withMode @mode (==) (==)
      op lhs rhs

instance KnownNat n => Ord (IntN' C n) where
  compare = curry $ \case
    (IntZ, IntZ) -> EQ
    (IntP lhs, IntP rhs) -> compare lhs rhs

instance (Unified.DecideEvalMode mode, KnownNat n) => Show (IntN' mode n) where
  show = \case
    IntZ -> "0x"
    IntP lhs -> Unified.withMode @mode show show $ lhs

instance (Unified.DecideEvalMode mode, KnownNat n) => SymEq (IntN' mode n) where
  (.==) = curry $ \case
    (IntZ, IntZ) -> true
    (IntP lhs, IntP rhs) -> do
      let eq = Unified.withMode @mode (.==) (.==)
      eq lhs rhs

instance (Unified.DecideEvalMode mode, KnownNat n) => SymOrd (IntN' mode n) where
  symCompare = curry $ \case
    (IntZ, IntZ) -> pure EQ
    (IntP lhs, IntP rhs) -> do
      let cmp = Unified.withMode @mode symCompare symCompare
      cmp lhs rhs

instance (Unified.DecideEvalMode mode, KnownNat n) => Num (IntN' mode n) where
  (+) = binary $ Unified.withMode @mode (+) (+)

  (*) = binary $ Unified.withMode @mode (*) (*)

  abs = unary $ Unified.withMode @mode abs abs

  signum = unary $ Unified.withMode @mode signum signum

  fromInteger value = do
    let op :: 1 <= n => Integer -> GetIntN mode n
        op = Unified.withMode @mode fromInteger fromInteger
    withSize' @n $ op value

  negate = unary $ Unified.withMode @mode negate negate

instance (Unified.DecideEvalMode mode, KnownNat n) => Bits (IntN' mode n) where
  (.&.) = binary $ Unified.withMode @mode (.&.) (.&.)

  (.|.) = binary $ Unified.withMode @mode (.|.) (.|.)

  xor = binary $ Unified.withMode @mode xor xor

  complement = unary $ Unified.withMode @mode complement complement

  shift value idx = do
    let op :: 1 <= n => GetIntN mode n -> Int -> GetIntN mode n
        op = Unified.withMode @mode shift shift
    unary (flip op idx) value

  rotate value idx = do
    let op :: 1 <= n => GetIntN mode n -> Int -> GetIntN mode n
        op = Unified.withMode @mode rotate rotate
    unary (flip op idx) value

  bitSize = finiteBitSize

  bitSizeMaybe = pure . finiteBitSize

  isSigned _ = True

  testBit value idx = case value of
    IntZ -> False
    IntP value' -> do
      let op = Unified.withMode @mode testBit testBit
      op value' idx

  bit idx = do
    let op :: 1 <= n => Int -> GetIntN mode n
        op = Unified.withMode @mode bit bit
    withSize' @n $ op idx

  popCount = \case
    IntZ -> 0
    IntP value -> Unified.withMode @mode popCount popCount $ value

instance (Unified.DecideEvalMode mode, KnownNat n) => FiniteBits (IntN' mode n) where
  finiteBitSize _ = fromIntegral (natVal @n Proxy)

instance KnownNat n => ITEOp (IntN' S n) where
  symIte conditional = binary $ symIte conditional

instance KnownNat n => SymFiniteBits (IntN' S n) where
  symTestBit value idx = case value of
    IntZ -> false
    IntP value' -> symTestBit value' idx

  symSetBitTo value idx set = case value of
    IntZ -> IntZ
    IntP value' -> IntP $ symSetBitTo value' idx set

  symFromBits bits = withSize' @n $ symFromBits bits

instance (Unified.DecideEvalMode mode, KnownNat n) => SymShift (IntN' mode n) where
  symShift = binary $ Unified.withMode @mode symShift symShift
  symShiftNegated = binary $ Unified.withMode @mode symShiftNegated symShiftNegated

instance (Unified.DecideEvalMode mode, KnownNat n) => SymRotate (IntN' mode n) where
  symRotate = binary $ Unified.withMode @mode symRotate symRotate
  symRotateNegated = binary $ Unified.withMode @mode symRotateNegated symRotateNegated

instance (Unified.DecideEvalMode mode, KnownNat n) => EvalSym (IntN' mode n) where
  evalSym fill model = do
    let op :: 1 <= n => Bool -> Model -> GetIntN mode n -> GetIntN mode n
        op = Unified.withMode @mode evalSym evalSym
    unary $ op fill model

instance (Unified.DecideEvalMode mode, KnownNat n) => Mergeable (IntN' mode n) where
  rootStrategy = do
    let concrete :: MergingStrategy (IntN' C n)
        concrete = SortedStrategy id $ (\_ -> SimpleStrategy $ \_ t _ -> t)

    let symbolic :: MergingStrategy (IntN' S n)
        symbolic = SimpleStrategy $ \cond -> binary $ symIte cond

    Unified.withMode @mode concrete symbolic

instance KnownNat n => SimpleMergeable (IntN' S n) where
  mrgIte cond = binary $ mrgIte cond

instance (KnownNat n, KnownNat n') => SymFromIntegral (IntN' S n) (IntN' S n') where
  symFromIntegral = \case
    IntZ -> withSize' 0
    IntP value -> withSize' $ symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (SymWordN n) (IntN' S n') where
  symFromIntegral value = withSize' $ symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (SymIntN n) (IntN' S n') where
  symFromIntegral value = withSize' $ symFromIntegral value

instance KnownNat n => SymFromIntegral SymInteger (IntN' S n) where
  symFromIntegral value = withSize' $ symFromIntegral value

instance KnownNat n => ToCon (IntN' S n) (IntN' C n) where
  toCon = \case
    IntZ -> pure IntZ
    IntP value -> IntP <$> toCon value

instance ToCon (IntN' mode n) (IntN' mode n) where
  toCon = pure

instance KnownNat n => ToSym (IntN' C n) (IntN' S n) where
  toSym = \case
    IntZ -> IntZ
    IntP value -> IntP $ toSym value

instance ToSym (IntN' mode n) (IntN' mode n) where
  toSym = id

instance ConRep (IntN' S n) where
  type ConType (IntN' S n) = IntN' C n
