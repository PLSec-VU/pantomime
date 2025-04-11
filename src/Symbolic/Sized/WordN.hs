{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Symbolic.Sized.WordN
  ( WordN' (..)
  ) where

import GHC.TypeNats (type (<=), Natural, KnownNat, natVal)

import Grisette hiding (fill)
import Grisette.Unified (EvalModeTag (..), GetWordN)
import qualified Grisette.Unified as Unified

import Data.Bits (Bits (..), FiniteBits (..))
import Data.Data (Proxy(..))

import Symbolic.Dict (withSize)

data WordN' (mode :: EvalModeTag) (n :: Natural) where
  WordZ :: WordN' mode 0
  WordP :: 1 <= n => GetWordN mode n -> WordN' mode n

binary
  :: forall mode n
   . (1 <= n => GetWordN mode n -> GetWordN mode n -> GetWordN mode n)
  -> WordN' mode n
  -> WordN' mode n
  -> WordN' mode n
binary op = curry $ \case
  (WordZ, WordZ) -> WordZ
  (WordP lhs, WordP rhs) -> WordP $ op lhs rhs

unary
  :: forall mode n
   . (1 <= n => GetWordN mode n -> GetWordN mode n)
  -> WordN' mode n
  -> WordN' mode n
unary op = \case
  WordZ -> WordZ
  WordP value -> WordP $ op value

withSize' :: forall n mode. KnownNat n => (1 <= n => GetWordN mode n) -> WordN' mode n
withSize' value = withSize @n WordZ (WordP value)

instance (Unified.DecideEvalMode mode, KnownNat n) => Eq (WordN' mode n) where
  (==) = curry $ \case
    (WordZ, WordZ) -> true
    (WordP lhs, WordP rhs) -> do
      let op = Unified.withMode @mode (==) (==)
      op lhs rhs

instance KnownNat n => Ord (WordN' C n) where
  compare = curry $ \case
    (WordZ, WordZ) -> EQ
    (WordP lhs, WordP rhs) -> compare lhs rhs

instance (Unified.DecideEvalMode mode, KnownNat n) => Show (WordN' mode n) where
  show = \case
    WordZ -> "0x"
    WordP lhs -> Unified.withMode @mode show show $ lhs

instance (Unified.DecideEvalMode mode, KnownNat n) => SymEq (WordN' mode n) where
  (.==) = curry $ \case
    (WordZ, WordZ) -> true
    (WordP lhs, WordP rhs) -> do
      let eq = Unified.withMode @mode (.==) (.==)
      eq lhs rhs

instance (Unified.DecideEvalMode mode, KnownNat n) => SymOrd (WordN' mode n) where
  symCompare = curry $ \case
    (WordZ, WordZ) -> pure EQ
    (WordP lhs, WordP rhs) -> do
      let cmp = Unified.withMode @mode symCompare symCompare
      cmp lhs rhs

instance (Unified.DecideEvalMode mode, KnownNat n) => Num (WordN' mode n) where
  (+) = binary $ Unified.withMode @mode (+) (+)

  (*) = binary $ Unified.withMode @mode (*) (*)

  abs = unary $ Unified.withMode @mode abs abs

  signum = unary $ Unified.withMode @mode signum signum

  fromInteger value = do
    let op :: 1 <= n => Integer -> GetWordN mode n
        op = Unified.withMode @mode fromInteger fromInteger
    withSize' @n $ op value

  negate = unary $ Unified.withMode @mode negate negate

instance (Unified.DecideEvalMode mode, KnownNat n) => Bits (WordN' mode n) where
  (.&.) = binary $ Unified.withMode @mode (.&.) (.&.)

  (.|.) = binary $ Unified.withMode @mode (.|.) (.|.)

  xor = binary $ Unified.withMode @mode xor xor

  complement = unary $ Unified.withMode @mode complement complement

  shift value idx = do
    let op :: 1 <= n => GetWordN mode n -> Int -> GetWordN mode n
        op = Unified.withMode @mode shift shift
    unary (flip op idx) value

  rotate value idx = do
    let op :: 1 <= n => GetWordN mode n -> Int -> GetWordN mode n
        op = Unified.withMode @mode rotate rotate
    unary (flip op idx) value

  bitSize = finiteBitSize

  bitSizeMaybe = pure . finiteBitSize

  isSigned _ = True

  testBit value idx = case value of
    WordZ -> False
    WordP value' -> do
      let op = Unified.withMode @mode testBit testBit
      op value' idx

  bit idx = do
    let op :: 1 <= n => Int -> GetWordN mode n
        op = Unified.withMode @mode bit bit
    withSize' @n $ op idx

  popCount = \case
    WordZ -> 0
    WordP value -> Unified.withMode @mode popCount popCount $ value

instance (Unified.DecideEvalMode mode, KnownNat n) => FiniteBits (WordN' mode n) where
  finiteBitSize _ = fromIntegral (natVal @n Proxy)

instance KnownNat n => ITEOp (WordN' S n) where
  symIte conditional = binary $ symIte conditional

instance KnownNat n => SymFiniteBits (WordN' S n) where
  symTestBit value idx = case value of
    WordZ -> false
    WordP value' -> symTestBit value' idx

  symSetBitTo value idx set = case value of
    WordZ -> WordZ
    WordP value' -> WordP $ symSetBitTo value' idx set

  symFromBits bits = withSize' @n $ symFromBits bits

instance (Unified.DecideEvalMode mode, KnownNat n) => SymShift (WordN' mode n) where
  symShift = binary $ Unified.withMode @mode symShift symShift
  symShiftNegated = binary $ Unified.withMode @mode symShiftNegated symShiftNegated

instance (Unified.DecideEvalMode mode, KnownNat n) => SymRotate (WordN' mode n) where
  symRotate = binary $ Unified.withMode @mode symRotate symRotate
  symRotateNegated = binary $ Unified.withMode @mode symRotateNegated symRotateNegated

instance (Unified.DecideEvalMode mode, KnownNat n) => EvalSym (WordN' mode n) where
  evalSym fill model = do
    let op :: 1 <= n => Bool -> Model -> GetWordN mode n -> GetWordN mode n
        op = Unified.withMode @mode evalSym evalSym
    unary $ op fill model

instance (Unified.DecideEvalMode mode, KnownNat n) => Mergeable (WordN' mode n) where
  rootStrategy = do
    let concrete :: MergingStrategy (WordN' C n)
        concrete = SortedStrategy id $ (\_ -> SimpleStrategy $ \_ t _ -> t)

    let symbolic :: MergingStrategy (WordN' S n)
        symbolic = SimpleStrategy $ \cond -> binary $ symIte cond

    Unified.withMode @mode concrete symbolic

instance KnownNat n => SimpleMergeable (WordN' S n) where
  mrgIte cond = binary $ mrgIte cond

instance (KnownNat n, KnownNat n') => SymFromIntegral (WordN' S n) (WordN' S n') where
  symFromIntegral = \case
    WordZ -> withSize' 0
    WordP value -> withSize' $ symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (SymWordN n) (WordN' S n') where
  symFromIntegral value = withSize' $ symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (SymIntN n) (WordN' S n') where
  symFromIntegral value = withSize' $ symFromIntegral value

instance KnownNat n => SymFromIntegral SymInteger (WordN' S n) where
  symFromIntegral value = withSize' $ symFromIntegral value

instance KnownNat n => ToCon (WordN' S n) (WordN' C n) where
  toCon = \case
    WordZ -> pure WordZ
    WordP value -> WordP <$> toCon value

instance ToCon (WordN' mode n) (WordN' mode n) where
  toCon = pure

instance KnownNat n => ToSym (WordN' C n) (WordN' S n) where
  toSym = \case
    WordZ -> WordZ
    WordP value -> WordP $ toSym value

instance ToSym (WordN' mode n) (WordN' mode n) where
  toSym = id

instance ConRep (WordN' S n) where
  type ConType (WordN' S n) = WordN' C n
