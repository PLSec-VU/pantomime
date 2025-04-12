{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Symbolic.Sized.BitVector
  ( IntN' (..)
  , WordN' (..)
  ) where

import GHC.TypeNats (type (<=), type (+), Natural, KnownNat, natVal)

import Grisette hiding (fill)
import Grisette.Unified (EvalModeTag (..), GetIntN, GetWordN)
import qualified Grisette.Unified as Unified

import Data.Bits (Bits (..), FiniteBits (..))
import Data.Data (Proxy(..))

import Symbolic.Dict (withSize, Dict (..), unsafeDict)
import Symbolic.Sized.Class

data IntN' (mode :: EvalModeTag) (n :: Natural) where
  IntZ :: IntN' mode 0
  IntP :: 1 <= n => GetIntN mode n -> IntN' mode n

binaryI
  :: forall mode n
   . (1 <= n => GetIntN mode n -> GetIntN mode n -> GetIntN mode n)
  -> IntN' mode n
  -> IntN' mode n
  -> IntN' mode n
binaryI op = curry $ \case
  (IntZ, IntZ) -> IntZ
  (IntP lhs, IntP rhs) -> IntP $ op lhs rhs

unaryI
  :: forall mode n
   . (1 <= n => GetIntN mode n -> GetIntN mode n)
  -> IntN' mode n
  -> IntN' mode n
unaryI op = \case
  IntZ -> IntZ
  IntP value -> IntP $ op value

withSizeI :: forall n mode. KnownNat n => (1 <= n => GetIntN mode n) -> IntN' mode n
withSizeI value = withSize @n IntZ (IntP value)

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
  (+) = binaryI $ Unified.withMode @mode (+) (+)

  (*) = binaryI $ Unified.withMode @mode (*) (*)

  abs = unaryI $ Unified.withMode @mode abs abs

  signum = unaryI $ Unified.withMode @mode signum signum

  fromInteger value = do
    let op :: 1 <= n => Integer -> GetIntN mode n
        op = Unified.withMode @mode fromInteger fromInteger
    withSizeI @n $ op value

  negate = unaryI $ Unified.withMode @mode negate negate

instance (Unified.DecideEvalMode mode, KnownNat n) => Bits (IntN' mode n) where
  (.&.) = binaryI $ Unified.withMode @mode (.&.) (.&.)

  (.|.) = binaryI $ Unified.withMode @mode (.|.) (.|.)

  xor = binaryI $ Unified.withMode @mode xor xor

  complement = unaryI $ Unified.withMode @mode complement complement

  shift value idx = do
    let op :: 1 <= n => GetIntN mode n -> Int -> GetIntN mode n
        op = Unified.withMode @mode shift shift
    unaryI (flip op idx) value

  rotate value idx = do
    let op :: 1 <= n => GetIntN mode n -> Int -> GetIntN mode n
        op = Unified.withMode @mode rotate rotate
    unaryI (flip op idx) value

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
    withSizeI @n $ op idx

  popCount = \case
    IntZ -> 0
    IntP value -> Unified.withMode @mode popCount popCount $ value

instance (Unified.DecideEvalMode mode, KnownNat n) => FiniteBits (IntN' mode n) where
  finiteBitSize _ = fromIntegral (natVal @n Proxy)

instance KnownNat n => ITEOp (IntN' S n) where
  symIte conditional = binaryI $ symIte conditional

instance KnownNat n => SymFiniteBits (IntN' S n) where
  symTestBit value idx = case value of
    IntZ -> false
    IntP value' -> symTestBit value' idx

  symSetBitTo value idx set = case value of
    IntZ -> IntZ
    IntP value' -> IntP $ symSetBitTo value' idx set

  symFromBits bits = withSizeI @n $ symFromBits bits

instance (Unified.DecideEvalMode mode, KnownNat n) => SymShift (IntN' mode n) where
  symShift = binaryI $ Unified.withMode @mode symShift symShift
  symShiftNegated = binaryI $ Unified.withMode @mode symShiftNegated symShiftNegated

instance (Unified.DecideEvalMode mode, KnownNat n) => SymRotate (IntN' mode n) where
  symRotate = binaryI $ Unified.withMode @mode symRotate symRotate
  symRotateNegated = binaryI $ Unified.withMode @mode symRotateNegated symRotateNegated

instance (Unified.DecideEvalMode mode, KnownNat n) => EvalSym (IntN' mode n) where
  evalSym fill model = do
    let op :: 1 <= n => Bool -> Model -> GetIntN mode n -> GetIntN mode n
        op = Unified.withMode @mode evalSym evalSym
    unaryI $ op fill model

instance (Unified.DecideEvalMode mode, KnownNat n) => Mergeable (IntN' mode n) where
  rootStrategy = do
    let concrete :: MergingStrategy (IntN' C n)
        concrete = SortedStrategy id $ (\_ -> SimpleStrategy $ \_ t _ -> t)

    let symbolic :: MergingStrategy (IntN' S n)
        symbolic = SimpleStrategy $ \cond -> binaryI $ symIte cond

    Unified.withMode @mode concrete symbolic

instance KnownNat n => SimpleMergeable (IntN' S n) where
  mrgIte cond = binaryI $ mrgIte cond

instance (KnownNat n, KnownNat n') => SymFromIntegral (IntN' S n) (IntN' S n') where
  symFromIntegral = \case
    IntZ -> withSizeI 0
    IntP value -> withSizeI $ symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (SymWordN n) (IntN' S n') where
  symFromIntegral value = withSizeI $ symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (IntN' S n') (SymWordN n) where
  symFromIntegral = \case
    IntZ -> 0
    IntP value -> symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (SymIntN n) (IntN' S n') where
  symFromIntegral value = withSizeI $ symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (IntN' S n') (SymIntN n) where
  symFromIntegral = \case
    IntZ -> 0
    IntP value -> symFromIntegral value

instance KnownNat n => SymFromIntegral SymInteger (IntN' S n) where
  symFromIntegral value = withSizeI $ symFromIntegral value

instance KnownNat n => SymFromIntegral (IntN' S n) SymInteger where
  symFromIntegral = \case
    IntZ -> 0
    IntP value -> symFromIntegral value

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

instance Unified.DecideEvalMode mode => SizedBV' (IntN' mode) where
  sizedBVConcat'
    :: forall l r
     . KnownNat l
    => KnownNat r
    => IntN' mode l
    -> IntN' mode r
    -> IntN' mode (l + r)
  sizedBVConcat' = curry $ \case
    (IntZ, IntZ) -> IntZ
    (IntZ, rhs) -> rhs
    (lhs, IntZ) -> lhs
    (IntP lhs, IntP rhs) -> do
      let op :: GetIntN mode l -> GetIntN mode r -> GetIntN mode (l + r)
          op = Unified.withMode @mode sizedBVConcat sizedBVConcat
      -- SAFETY: Haskell isn't able to infer that the sum of two positives is
      -- also positive, so we just unsafely get the proof for it.
      case unsafeDict @(1 <= l + r) of
        Dict -> IntP $ op lhs rhs

  sizedBVZext'
    :: forall l r
     . KnownNat l
    => KnownNat r
    => l <= r
    => IntN' mode l
    -> IntN' mode r
  sizedBVZext' = \case
    IntZ -> do
      let op :: 1 <= r => GetIntN mode r
          op = Unified.withMode @mode
            (sizedBVZext @_ @1 Proxy 0)
            (sizedBVZext @_ @1 Proxy 0)
      withSizeI op
    IntP value -> do
      let op :: GetIntN mode l -> GetIntN mode r
          op = Unified.withMode @mode
            (sizedBVZext @_ @l @r Proxy)
            (sizedBVZext @_ @l @r Proxy)
      withSizeI $ op value

  sizedBVSext'
    :: forall l r
     . KnownNat l
    => KnownNat r
    => l <= r
    => IntN' mode l
    -> IntN' mode r
  sizedBVSext' = \case
    IntZ -> do
      let op :: 1 <= r => GetIntN mode r
          op = Unified.withMode @mode
            (sizedBVSext @_ @1 Proxy 0)
            (sizedBVSext @_ @1 Proxy 0)
      withSizeI op
    IntP value -> do
      let op :: GetIntN mode l -> GetIntN mode r
          op = Unified.withMode @mode
            (sizedBVSext @_ @l @r Proxy)
            (sizedBVSext @_ @l @r Proxy)
      withSizeI $ op value

  sizedBVExt' = sizedBVSext'

  sizedBVSelect''
    :: forall idx width n
     . KnownNat idx
    => KnownNat width
    => KnownNat n
    => idx + width <= n
    => Proxy idx
    -> Proxy width
    -> IntN' mode n
    -> IntN' mode width
  sizedBVSelect'' _ _ = \case
    IntZ -> case unsafeDict @(width ~ 0) of
      Dict -> IntZ
    IntP value -> do
      let op :: 1 <= width => GetIntN mode n -> GetIntN mode width
          op = Unified.withMode @mode
            (sizedBVSelect @_ @n @idx @width Proxy Proxy)
            (sizedBVSelect @_ @n @idx @width Proxy Proxy)
      withSizeI $ op value

data WordN' (mode :: EvalModeTag) (n :: Natural) where
  WordZ :: WordN' mode 0
  WordP :: 1 <= n => GetWordN mode n -> WordN' mode n

binaryW
  :: forall mode n
   . (1 <= n => GetWordN mode n -> GetWordN mode n -> GetWordN mode n)
  -> WordN' mode n
  -> WordN' mode n
  -> WordN' mode n
binaryW op = curry $ \case
  (WordZ, WordZ) -> WordZ
  (WordP lhs, WordP rhs) -> WordP $ op lhs rhs

unaryW
  :: forall mode n
   . (1 <= n => GetWordN mode n -> GetWordN mode n)
  -> WordN' mode n
  -> WordN' mode n
unaryW op = \case
  WordZ -> WordZ
  WordP value -> WordP $ op value

withSizeW :: forall n mode. KnownNat n => (1 <= n => GetWordN mode n) -> WordN' mode n
withSizeW value = withSize @n WordZ (WordP value)

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
  (+) = binaryW $ Unified.withMode @mode (+) (+)

  (*) = binaryW $ Unified.withMode @mode (*) (*)

  abs = unaryW $ Unified.withMode @mode abs abs

  signum = unaryW $ Unified.withMode @mode signum signum

  fromInteger value = do
    let op :: 1 <= n => Integer -> GetWordN mode n
        op = Unified.withMode @mode fromInteger fromInteger
    withSizeW @n $ op value

  negate = unaryW $ Unified.withMode @mode negate negate

instance (Unified.DecideEvalMode mode, KnownNat n) => Bits (WordN' mode n) where
  (.&.) = binaryW $ Unified.withMode @mode (.&.) (.&.)

  (.|.) = binaryW $ Unified.withMode @mode (.|.) (.|.)

  xor = binaryW $ Unified.withMode @mode xor xor

  complement = unaryW $ Unified.withMode @mode complement complement

  shift value idx = do
    let op :: 1 <= n => GetWordN mode n -> Int -> GetWordN mode n
        op = Unified.withMode @mode shift shift
    unaryW (flip op idx) value

  rotate value idx = do
    let op :: 1 <= n => GetWordN mode n -> Int -> GetWordN mode n
        op = Unified.withMode @mode rotate rotate
    unaryW (flip op idx) value

  bitSize = finiteBitSize

  bitSizeMaybe = pure . finiteBitSize

  isSigned _ = False

  testBit value idx = case value of
    WordZ -> False
    WordP value' -> do
      let op = Unified.withMode @mode testBit testBit
      op value' idx

  bit idx = do
    let op :: 1 <= n => Int -> GetWordN mode n
        op = Unified.withMode @mode bit bit
    withSizeW @n $ op idx

  popCount = \case
    WordZ -> 0
    WordP value -> Unified.withMode @mode popCount popCount $ value

instance (Unified.DecideEvalMode mode, KnownNat n) => FiniteBits (WordN' mode n) where
  finiteBitSize _ = fromIntegral (natVal @n Proxy)

instance KnownNat n => ITEOp (WordN' S n) where
  symIte conditional = binaryW $ symIte conditional

instance KnownNat n => SymFiniteBits (WordN' S n) where
  symTestBit value idx = case value of
    WordZ -> false
    WordP value' -> symTestBit value' idx

  symSetBitTo value idx set = case value of
    WordZ -> WordZ
    WordP value' -> WordP $ symSetBitTo value' idx set

  symFromBits bits = withSizeW @n $ symFromBits bits

instance (Unified.DecideEvalMode mode, KnownNat n) => SymShift (WordN' mode n) where
  symShift = binaryW $ Unified.withMode @mode symShift symShift
  symShiftNegated = binaryW $ Unified.withMode @mode symShiftNegated symShiftNegated

instance (Unified.DecideEvalMode mode, KnownNat n) => SymRotate (WordN' mode n) where
  symRotate = binaryW $ Unified.withMode @mode symRotate symRotate
  symRotateNegated = binaryW $ Unified.withMode @mode symRotateNegated symRotateNegated

instance (Unified.DecideEvalMode mode, KnownNat n) => EvalSym (WordN' mode n) where
  evalSym fill model = do
    let op :: 1 <= n => Bool -> Model -> GetWordN mode n -> GetWordN mode n
        op = Unified.withMode @mode evalSym evalSym
    unaryW $ op fill model

instance (Unified.DecideEvalMode mode, KnownNat n) => Mergeable (WordN' mode n) where
  rootStrategy = do
    let concrete :: MergingStrategy (WordN' C n)
        concrete = SortedStrategy id $ (\_ -> SimpleStrategy $ \_ t _ -> t)

    let symbolic :: MergingStrategy (WordN' S n)
        symbolic = SimpleStrategy $ \cond -> binaryW $ symIte cond

    Unified.withMode @mode concrete symbolic

instance KnownNat n => SimpleMergeable (WordN' S n) where
  mrgIte cond = binaryW $ mrgIte cond

instance (KnownNat n, KnownNat n') => SymFromIntegral (WordN' S n) (WordN' S n') where
  symFromIntegral = \case
    WordZ -> withSizeW 0
    WordP value -> withSizeW $ symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (SymWordN n) (WordN' S n') where
  symFromIntegral value = withSizeW $ symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (WordN' S n') (SymWordN n) where
  symFromIntegral = \case
    WordZ -> 0
    WordP value -> symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (SymIntN n) (WordN' S n') where
  symFromIntegral value = withSizeW $ symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (WordN' S n') (SymIntN n) where
  symFromIntegral = \case
    WordZ -> 0
    WordP value -> symFromIntegral value

instance KnownNat n => SymFromIntegral SymInteger (WordN' S n) where
  symFromIntegral value = withSizeW $ symFromIntegral value

instance KnownNat n => SymFromIntegral (WordN' S n) SymInteger where
  symFromIntegral = \case
    WordZ -> 0
    WordP value -> symFromIntegral value

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

instance Unified.DecideEvalMode mode => SizedBV' (WordN' mode) where
  sizedBVConcat'
    :: forall l r
     . KnownNat l
    => KnownNat r
    => WordN' mode l
    -> WordN' mode r
    -> WordN' mode (l + r)
  sizedBVConcat' = curry $ \case
    (WordZ, WordZ) -> WordZ
    (WordZ, rhs) -> rhs
    (lhs, WordZ) -> lhs
    (WordP lhs, WordP rhs) -> do
      let op :: GetWordN mode l -> GetWordN mode r -> GetWordN mode (l + r)
          op = Unified.withMode @mode sizedBVConcat sizedBVConcat
      -- SAFETY: Haskell isn't able to infer that the sum of two positives is
      -- also positive, so we just unsafely get the proof for it.
      case unsafeDict @(1 <= l + r) of
        Dict -> WordP $ op lhs rhs

  sizedBVZext'
    :: forall l r
     . KnownNat l
    => KnownNat r
    => l <= r
    => WordN' mode l
    -> WordN' mode r
  sizedBVZext' = \case
    WordZ -> do
      let op :: 1 <= r => GetWordN mode r
          op = Unified.withMode @mode
            (sizedBVZext @_ @1 Proxy 0)
            (sizedBVZext @_ @1 Proxy 0)
      withSizeW op
    WordP value -> do
      let op :: GetWordN mode l -> GetWordN mode r
          op = Unified.withMode @mode
            (sizedBVZext @_ @l @r Proxy)
            (sizedBVZext @_ @l @r Proxy)
      withSizeW $ op value

  sizedBVSext'
    :: forall l r
     . KnownNat l
    => KnownNat r
    => l <= r
    => WordN' mode l
    -> WordN' mode r
  sizedBVSext' = \case
    WordZ -> do
      let op :: 1 <= r => GetWordN mode r
          op = Unified.withMode @mode
            (sizedBVSext @_ @1 Proxy 0)
            (sizedBVSext @_ @1 Proxy 0)
      withSizeW op
    WordP value -> do
      let op :: GetWordN mode l -> GetWordN mode r
          op = Unified.withMode @mode
            (sizedBVSext @_ @l @r Proxy)
            (sizedBVSext @_ @l @r Proxy)
      withSizeW $ op value

  sizedBVExt' = sizedBVZext'

  sizedBVSelect''
    :: forall idx width n
     . KnownNat idx
    => KnownNat width
    => KnownNat n
    => idx + width <= n
    => Proxy idx
    -> Proxy width
    -> WordN' mode n
    -> WordN' mode width
  sizedBVSelect'' _ _ = \case
    WordZ -> case unsafeDict @(width ~ 0) of
      Dict -> WordZ
    WordP value -> do
      let op :: 1 <= width => GetWordN mode n -> GetWordN mode width
          op = Unified.withMode @mode
            (sizedBVSelect @_ @n @idx @width Proxy Proxy)
            (sizedBVSelect @_ @n @idx @width Proxy Proxy)
      withSizeW $ op value

instance (Unified.DecideEvalMode mode, KnownNat n) => SignConversion (WordN' mode n) (IntN' mode n) where
  toSigned = \case
    WordZ -> IntZ
    WordP value -> do
      let op :: GetWordN mode n -> GetIntN mode n
          op = Unified.withMode @mode toSigned toSigned
      IntP $ op value

  toUnsigned = \case
    IntZ -> WordZ
    IntP value -> do
      let op :: GetIntN mode n -> GetWordN mode n
          op = Unified.withMode @mode toUnsigned toUnsigned
      WordP $ op value
