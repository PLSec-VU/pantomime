{-# LANGUAGE UndecidableInstances #-}

module Pantomime.Grisette.BitVector
  ( IntN (..)
  , binaryI
  , unaryI
  , withSizeI

  , WordN (..)
  , binaryW
  , unaryW
  , withSizeW
  ) where

import GHC.TypeNats (type (<=), type (+), Natural, KnownNat, natVal)
import GHC.Prim.Exception (raiseDivZero)

import Grisette qualified (SizedBV (..))
import Grisette
  ( SymEq (..)
  , SymOrd (..)
  , SymFiniteBits (..)
  , SymShift (..)
  , SymRotate (..)
  , SymFromIntegral (..)
  , SignConversion (..)
  , ConRep (..)
  , ToCon (..)
  , ToSym (..)
  , EvalSym (..)
  , Model
  , Mergeable (..)
  , SimpleMergeable (..)
  , MergingStrategy (..)
  , ITEOp (..)
  , GenSym (..)
  , GenSymSimple (..)
  , SymWordN
  , SymIntN
  , SymInteger
  , SymBool
  , BitCast (..)
  , Solvable (..)
  , true
  , false
  )
import Grisette.Unified
  ( EvalModeTag (..)
  , GetIntN
  , GetWordN
  , DecideEvalMode (..)
  , withMode
  )

import Data.Bits (Bits (..), FiniteBits (..))
import Data.Data (Proxy(..))
import Data.Bifunctor (Bifunctor(..))
import Data.String (IsString (..))

import Pantomime.Dict (withSize, Dict (..), unsafeDict)
import Pantomime.Grisette.SizedBV

-- | Sized integer primitive.
--
-- Compared to Grisette 'SymIntN' and 'IntN', this allows for zero-sized
-- bitvectors. Additionally, it uses the unified interface to both represent
-- the symbolic and non-symbolic version, as dictated by the 'EvalModeTag'.
data IntN (mode :: EvalModeTag) (n :: Natural) where
  IntZ :: IntN mode 0
  IntP :: 1 <= n => GetIntN mode n -> IntN mode n

-- | Helper function to wrap a binary function over Grisette sized integers.
binaryI
  :: forall mode n
   . (1 <= n => GetIntN mode n -> GetIntN mode n -> GetIntN mode n)
  -> IntN mode n
  -> IntN mode n
  -> IntN mode n
binaryI op = curry $ \case
  (IntZ, IntZ) -> IntZ
  (IntP lhs, IntP rhs) -> IntP $ op lhs rhs

-- | Helper function to wrap a unary function over Grisette sized integers.
unaryI
  :: forall mode n
   . (1 <= n => GetIntN mode n -> GetIntN mode n)
  -> IntN mode n
  -> IntN mode n
unaryI op = \case
  IntZ -> IntZ
  IntP value -> IntP $ op value

-- | Helper function to wrap a Grisette sized integers value.
withSizeI
  :: forall n mode
   . KnownNat n
  => (1 <= n => GetIntN mode n)
  -> IntN mode n
withSizeI value = withSize @n IntZ $ IntP value

instance (DecideEvalMode mode, KnownNat n) => Eq (IntN mode n) where
  (==) = curry $ \case
    (IntZ, IntZ) -> true
    (IntP lhs, IntP rhs) -> do
      let op = withMode @mode (==) (==)
      op lhs rhs

instance KnownNat n => Ord (IntN C n) where
  compare = curry $ \case
    (IntZ, IntZ) -> EQ
    (IntP lhs, IntP rhs) -> compare lhs rhs

instance (DecideEvalMode mode, KnownNat n) => Show (IntN mode n) where
  show = \case
    IntZ -> "0x"
    IntP lhs -> withMode @mode show show $ lhs

instance (DecideEvalMode mode, KnownNat n) => SymEq (IntN mode n) where
  (.==) = curry $ \case
    (IntZ, IntZ) -> true
    (IntP lhs, IntP rhs) -> do
      let eq = withMode @mode (.==) (.==)
      eq lhs rhs

instance (DecideEvalMode mode, KnownNat n) => SymOrd (IntN mode n) where
  symCompare = curry $ \case
    (IntZ, IntZ) -> pure EQ
    (IntP lhs, IntP rhs) -> do
      let cmp = withMode @mode symCompare symCompare
      cmp lhs rhs

instance (DecideEvalMode mode, KnownNat n) => Num (IntN mode n) where
  (+) = binaryI $ withMode @mode (+) (+)

  (*) = binaryI $ withMode @mode (*) (*)

  abs = unaryI $ withMode @mode abs abs

  signum = unaryI $ withMode @mode signum signum

  fromInteger value = do
    let op :: 1 <= n => Integer -> GetIntN mode n
        op = withMode @mode fromInteger fromInteger
    withSizeI @n $ op value

  negate = unaryI $ withMode @mode negate negate

instance (DecideEvalMode mode, KnownNat n) => Bits (IntN mode n) where
  (.&.) = binaryI $ withMode @mode (.&.) (.&.)

  (.|.) = binaryI $ withMode @mode (.|.) (.|.)

  xor = binaryI $ withMode @mode xor xor

  complement = unaryI $ withMode @mode complement complement

  shift value idx = do
    let op :: 1 <= n => GetIntN mode n -> Int -> GetIntN mode n
        op = withMode @mode shift shift
    unaryI (flip op idx) value

  rotate value idx = do
    let op :: 1 <= n => GetIntN mode n -> Int -> GetIntN mode n
        op = withMode @mode rotate rotate
    unaryI (flip op idx) value

  bitSize = finiteBitSize

  bitSizeMaybe = pure . finiteBitSize

  isSigned _ = True

  testBit value idx = case value of
    IntZ -> False
    IntP value' -> do
      let op = withMode @mode testBit testBit
      op value' idx

  bit idx = do
    let op :: 1 <= n => Int -> GetIntN mode n
        op = withMode @mode bit bit
    withSizeI @n $ op idx

  popCount = \case
    IntZ -> 0
    IntP value -> withMode @mode popCount popCount $ value

instance (DecideEvalMode mode, KnownNat n) => FiniteBits (IntN mode n) where
  finiteBitSize _ = fromIntegral (natVal @n Proxy)

instance KnownNat n => ITEOp (IntN S n) where
  symIte conditional = binaryI $ symIte conditional

instance KnownNat n => SymFiniteBits (IntN S n) where
  symTestBit value idx = case value of
    IntZ -> false
    IntP value' -> symTestBit value' idx

  symSetBitTo value idx set = case value of
    IntZ -> IntZ
    IntP value' -> IntP $ symSetBitTo value' idx set

  symFromBits bits = withSizeI @n $ symFromBits bits

instance (DecideEvalMode mode, KnownNat n) => SymShift (IntN mode n) where
  symShift = binaryI $ withMode @mode symShift symShift
  symShiftNegated = binaryI $ withMode @mode symShiftNegated symShiftNegated

instance (DecideEvalMode mode, KnownNat n) => SymRotate (IntN mode n) where
  symRotate = binaryI $ withMode @mode symRotate symRotate
  symRotateNegated = binaryI $ withMode @mode symRotateNegated symRotateNegated

instance (DecideEvalMode mode, KnownNat n) => EvalSym (IntN mode n) where
  evalSym fill model = do
    let op :: 1 <= n => Bool -> Model -> GetIntN mode n -> GetIntN mode n
        op = withMode @mode evalSym evalSym
    unaryI $ op fill model

instance (DecideEvalMode mode, KnownNat n) => Mergeable (IntN mode n) where
  rootStrategy = do
    let concrete :: MergingStrategy (IntN C n)
        concrete = SortedStrategy id $ (\_ -> SimpleStrategy $ \_ t _ -> t)

    let symbolic :: MergingStrategy (IntN S n)
        symbolic = SimpleStrategy $ \cond -> binaryI $ symIte cond

    withMode @mode concrete symbolic

instance KnownNat n => SimpleMergeable (IntN S n) where
  mrgIte cond = binaryI $ mrgIte cond

instance (DecideEvalMode mode, KnownNat n, KnownNat n')
  => SymFromIntegral (IntN mode n) (IntN mode n') where
  symFromIntegral = \case
    IntZ -> withSizeI $ withMode @mode 0 0
    IntP value -> do
      let op :: 1 <= n' => GetIntN mode n -> GetIntN mode n'
          op = withMode @mode fromIntegral symFromIntegral
      withSizeI $ op value

instance (DecideEvalMode mode, KnownNat n, KnownNat n')
  => SymFromIntegral (WordN mode n) (IntN mode n') where
  symFromIntegral = \case
    WordZ -> withSizeI $ withMode @mode 0 0
    WordP value -> do
      let op :: 1 <= n' => GetWordN mode n -> GetIntN mode n'
          op = withMode @mode fromIntegral symFromIntegral
      withSizeI $ op value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (SymWordN n) (IntN S n') where
  symFromIntegral value = withSizeI $ symFromIntegral value

instance (KnownNat n, 1 <= n', KnownNat n') => SymFromIntegral (IntN S n) (SymWordN n') where
  symFromIntegral = \case
    IntZ -> 0
    IntP value -> symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (SymIntN n) (IntN S n') where
  symFromIntegral value = withSizeI $ symFromIntegral value

instance (KnownNat n, 1 <= n', KnownNat n') => SymFromIntegral (IntN S n) (SymIntN n') where
  symFromIntegral = \case
    IntZ -> 0
    IntP value -> symFromIntegral value

instance KnownNat n => SymFromIntegral SymInteger (IntN S n) where
  symFromIntegral value = withSizeI $ symFromIntegral value

instance KnownNat n => SymFromIntegral (IntN S n) SymInteger where
  symFromIntegral = \case
    IntZ -> 0
    IntP value -> symFromIntegral value

instance (DecideEvalMode mode, KnownNat n) => ToCon (IntN mode n) (IntN C n) where
  toCon = \case
    IntZ -> pure IntZ
    IntP value -> IntP <$> withMode @mode toCon toCon value

instance (DecideEvalMode mode, KnownNat n) => ToSym (IntN mode n) (IntN S n) where
  toSym = \case
    IntZ -> IntZ
    IntP value -> IntP $ withMode @mode toSym toSym value

instance ConRep (IntN S n) where
  type ConType (IntN S n) = IntN C n

instance DecideEvalMode mode => SizedBV (IntN mode) where
  sizedBVConcat @l @r = curry $ \case
    (IntZ, IntZ) -> IntZ
    (IntZ, rhs) -> rhs
    (lhs, IntZ) -> lhs
    (IntP lhs, IntP rhs) -> do
      let op :: GetIntN mode l -> GetIntN mode r -> GetIntN mode (l + r)
          op = withMode @mode Grisette.sizedBVConcat Grisette.sizedBVConcat
      -- SAFETY: Haskell isn't able to infer that the sum of two positives is
      -- also positive, so we just unsafely get the proof for it.
      case unsafeDict @(1 <= l + r) of
        Dict -> IntP $ op lhs rhs

  sizedBVZext @l @r = \case
    IntZ -> do
      let op :: 1 <= r => GetIntN mode r
          op = withMode @mode
            (Grisette.sizedBVZext @_ @1 Proxy 0)
            (Grisette.sizedBVZext @_ @1 Proxy 0)
      withSizeI op
    IntP value -> do
      let op :: GetIntN mode l -> GetIntN mode r
          op = withMode @mode
            (Grisette.sizedBVZext @_ @l @r Proxy)
            (Grisette.sizedBVZext @_ @l @r Proxy)
      withSizeI $ op value

  sizedBVSext @l @r = \case
    IntZ -> do
      let op :: 1 <= r => GetIntN mode r
          op = withMode @mode
            (Grisette.sizedBVSext @_ @1 Proxy 0)
            (Grisette.sizedBVSext @_ @1 Proxy 0)
      withSizeI op
    IntP value -> do
      let op :: GetIntN mode l -> GetIntN mode r
          op = withMode @mode
            (Grisette.sizedBVSext @_ @l @r Proxy)
            (Grisette.sizedBVSext @_ @l @r Proxy)
      withSizeI $ op value

  sizedBVExt = sizedBVSext

  sizedBVSelect @idx @width @n = \case
    IntZ -> case unsafeDict @(width ~ 0) of
      Dict -> IntZ
    IntP value -> do
      let op :: 1 <= width => GetIntN mode n -> GetIntN mode width
          op = withMode @mode
            (Grisette.sizedBVSelect @_ @n @idx @width Proxy Proxy)
            (Grisette.sizedBVSelect @_ @n @idx @width Proxy Proxy)
      withSizeI $ op value

instance (DecideEvalMode mode, KnownNat n) => GenSym (IntN mode n) (IntN mode n)

instance KnownNat n => GenSym () (IntN S n)

instance GenSymSimple (IntN mode n) (IntN mode n) where
  simpleFresh = pure

instance KnownNat n => GenSymSimple () (IntN S n) where
  simpleFresh spec = withSize @n
    (pure IntZ)
    (IntP <$> simpleFresh spec)

instance KnownNat n => Enum (IntN C n) where
  fromEnum = \case
    IntZ -> 0
    IntP value -> fromEnum value
  toEnum value = withSizeI $ toEnum value

instance KnownNat n => Real (IntN C n) where
  toRational = \case
    IntZ -> 0
    IntP value -> toRational value

instance KnownNat n => Integral (IntN C n) where
  quotRem = \cases
    IntZ IntZ -> raiseDivZero
    (IntP lhs) (IntP rhs) -> bimap IntP IntP $ quotRem lhs rhs

  toInteger = \case
    IntZ -> 0
    IntP value -> toInteger value

instance (DecideEvalMode mode, KnownNat n) => BitCast (WordN mode n) (IntN mode n) where
  bitCast = \case
    WordZ -> IntZ
    WordP value -> do
      let op = withMode @mode bitCast bitCast
      IntP $ op value

instance BitCast (IntN mode n) (IntN mode n) where
  bitCast = id

instance BitCast (IntN S 1) SymBool where
  bitCast (IntP value) = bitCast value

instance BitCast SymBool (IntN S 1) where
  bitCast = IntP . bitCast

instance KnownNat n => IsString (IntN S n) where
  fromString s = withSizeI @n $ fromString s

instance KnownNat n => Solvable (IntN C n) (IntN S n) where
  con = \case
    IntZ -> IntZ
    IntP value -> IntP $ con value

  conView = \case
    IntZ -> pure IntZ
    IntP value -> IntP <$> conView value

  sym symbol = withSizeI @n $ sym symbol

-- | Sized word primitive.
--
-- Compared to Grisette 'SymWordN' and 'WordN', this allows for zero-sized
-- bitvectors. Additionally, it uses the unified interface to both represent
-- the symbolic and non-symbolic version, as dictated by the 'EvalModeTag'.
data WordN (mode :: EvalModeTag) (n :: Natural) where
  WordZ :: WordN mode 0
  WordP :: 1 <= n => GetWordN mode n -> WordN mode n

-- | Helper function to wrap a binary function over Grisette sized words.
binaryW
  :: forall mode n
   . (1 <= n => GetWordN mode n -> GetWordN mode n -> GetWordN mode n)
  -> WordN mode n
  -> WordN mode n
  -> WordN mode n
binaryW op = curry $ \case
  (WordZ, WordZ) -> WordZ
  (WordP lhs, WordP rhs) -> WordP $ op lhs rhs

-- | Helper function to wrap a unary function over Grisette sized words.
unaryW
  :: forall mode n
   . (1 <= n => GetWordN mode n -> GetWordN mode n)
  -> WordN mode n
  -> WordN mode n
unaryW op = \case
  WordZ -> WordZ
  WordP value -> WordP $ op value

-- | Helper function to wrap a Grisette sized word value.
withSizeW
  :: forall n mode
   . KnownNat n
  => (1 <= n => GetWordN mode n)
  -> WordN mode n
withSizeW value = withSize @n WordZ $ WordP value

instance (DecideEvalMode mode, KnownNat n) => Eq (WordN mode n) where
  (==) = curry $ \case
    (WordZ, WordZ) -> true
    (WordP lhs, WordP rhs) -> do
      let op = withMode @mode (==) (==)
      op lhs rhs

instance KnownNat n => Ord (WordN C n) where
  compare = curry $ \case
    (WordZ, WordZ) -> EQ
    (WordP lhs, WordP rhs) -> compare lhs rhs

instance (DecideEvalMode mode, KnownNat n) => Show (WordN mode n) where
  show = \case
    WordZ -> "0x"
    WordP lhs -> withMode @mode show show $ lhs

instance (DecideEvalMode mode, KnownNat n) => SymEq (WordN mode n) where
  (.==) = curry $ \case
    (WordZ, WordZ) -> true
    (WordP lhs, WordP rhs) -> do
      let eq = withMode @mode (.==) (.==)
      eq lhs rhs

instance (DecideEvalMode mode, KnownNat n) => SymOrd (WordN mode n) where
  symCompare = curry $ \case
    (WordZ, WordZ) -> pure EQ
    (WordP lhs, WordP rhs) -> do
      let cmp = withMode @mode symCompare symCompare
      cmp lhs rhs

instance (DecideEvalMode mode, KnownNat n) => Num (WordN mode n) where
  (+) = binaryW $ withMode @mode (+) (+)

  (*) = binaryW $ withMode @mode (*) (*)

  abs = unaryW $ withMode @mode abs abs

  signum = unaryW $ withMode @mode signum signum

  fromInteger value = do
    let op :: 1 <= n => Integer -> GetWordN mode n
        op = withMode @mode fromInteger fromInteger
    withSizeW @n $ op value

  negate = unaryW $ withMode @mode negate negate

instance (DecideEvalMode mode, KnownNat n) => Bits (WordN mode n) where
  (.&.) = binaryW $ withMode @mode (.&.) (.&.)

  (.|.) = binaryW $ withMode @mode (.|.) (.|.)

  xor = binaryW $ withMode @mode xor xor

  complement = unaryW $ withMode @mode complement complement

  shift value idx = do
    let op :: 1 <= n => GetWordN mode n -> Int -> GetWordN mode n
        op = withMode @mode shift shift
    unaryW (flip op idx) value

  rotate value idx = do
    let op :: 1 <= n => GetWordN mode n -> Int -> GetWordN mode n
        op = withMode @mode rotate rotate
    unaryW (flip op idx) value

  bitSize = finiteBitSize

  bitSizeMaybe = pure . finiteBitSize

  isSigned _ = False

  testBit value idx = case value of
    WordZ -> False
    WordP value' -> do
      let op = withMode @mode testBit testBit
      op value' idx

  bit idx = do
    let op :: 1 <= n => Int -> GetWordN mode n
        op = withMode @mode bit bit
    withSizeW @n $ op idx

  popCount = \case
    WordZ -> 0
    WordP value -> withMode @mode popCount popCount $ value

instance (DecideEvalMode mode, KnownNat n) => FiniteBits (WordN mode n) where
  finiteBitSize _ = fromIntegral (natVal @n Proxy)

instance KnownNat n => ITEOp (WordN S n) where
  symIte conditional = binaryW $ symIte conditional

instance KnownNat n => SymFiniteBits (WordN S n) where
  symTestBit value idx = case value of
    WordZ -> false
    WordP value' -> symTestBit value' idx

  symSetBitTo value idx set = case value of
    WordZ -> WordZ
    WordP value' -> WordP $ symSetBitTo value' idx set

  symFromBits bits = withSizeW @n $ symFromBits bits

instance (DecideEvalMode mode, KnownNat n) => SymShift (WordN mode n) where
  symShift = binaryW $ withMode @mode symShift symShift
  symShiftNegated = binaryW $ withMode @mode symShiftNegated symShiftNegated

instance (DecideEvalMode mode, KnownNat n) => SymRotate (WordN mode n) where
  symRotate = binaryW $ withMode @mode symRotate symRotate
  symRotateNegated = binaryW $ withMode @mode symRotateNegated symRotateNegated

instance (DecideEvalMode mode, KnownNat n) => EvalSym (WordN mode n) where
  evalSym fill model = do
    let op :: 1 <= n => Bool -> Model -> GetWordN mode n -> GetWordN mode n
        op = withMode @mode evalSym evalSym
    unaryW $ op fill model

instance (DecideEvalMode mode, KnownNat n) => Mergeable (WordN mode n) where
  rootStrategy = do
    let concrete :: MergingStrategy (WordN C n)
        concrete = SortedStrategy id $ (\_ -> SimpleStrategy $ \_ t _ -> t)

    let symbolic :: MergingStrategy (WordN S n)
        symbolic = SimpleStrategy $ \cond -> binaryW $ symIte cond

    withMode @mode concrete symbolic

instance KnownNat n => SimpleMergeable (WordN S n) where
  mrgIte cond = binaryW $ mrgIte cond

instance (DecideEvalMode mode, KnownNat n, KnownNat n')
  => SymFromIntegral (WordN mode n) (WordN mode n') where
  symFromIntegral = \case
    WordZ -> withSizeW $ withMode @mode 0 0
    WordP value -> do
      let op :: 1 <= n' => GetWordN mode n -> GetWordN mode n'
          op = withMode @mode fromIntegral symFromIntegral
      withSizeW $ op value

instance (DecideEvalMode mode, KnownNat n, KnownNat n') => SymFromIntegral (IntN mode n) (WordN mode n') where
  symFromIntegral = \case
    IntZ -> withSizeW $ withMode @mode 0 0
    IntP value -> do
      let op :: 1 <= n' => GetIntN mode n -> GetWordN mode n'
          op = withMode @mode fromIntegral symFromIntegral
      withSizeW $ op value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (SymWordN n) (WordN S n') where
  symFromIntegral value = withSizeW $ symFromIntegral value

instance (KnownNat n, 1 <= n', KnownNat n') => SymFromIntegral (WordN S n) (SymWordN n') where
  symFromIntegral = \case
    WordZ -> 0
    WordP value -> symFromIntegral value

instance (KnownNat n, 1 <= n, KnownNat n') => SymFromIntegral (SymIntN n) (WordN S n') where
  symFromIntegral value = withSizeW $ symFromIntegral value

instance (KnownNat n, 1 <= n', KnownNat n') => SymFromIntegral (WordN S n) (SymIntN n') where
  symFromIntegral = \case
    WordZ -> 0
    WordP value -> symFromIntegral value

instance KnownNat n => SymFromIntegral SymInteger (WordN S n) where
  symFromIntegral value = withSizeW $ symFromIntegral value

instance KnownNat n => SymFromIntegral (WordN S n) SymInteger where
  symFromIntegral = \case
    WordZ -> 0
    WordP value -> symFromIntegral value

instance (DecideEvalMode mode, KnownNat n) => ToCon (WordN mode n) (WordN C n) where
  toCon = \case
    WordZ -> pure WordZ
    WordP value -> WordP <$> withMode @mode toCon toCon value

instance (DecideEvalMode mode, KnownNat n) => ToSym (WordN mode n) (WordN S n) where
  toSym = \case
    WordZ -> WordZ
    WordP value -> WordP $ withMode @mode toSym toSym value

instance ConRep (WordN S n) where
  type ConType (WordN S n) = WordN C n

instance DecideEvalMode mode => SizedBV (WordN mode) where
  sizedBVConcat @l @r = curry $ \case
    (WordZ, WordZ) -> WordZ
    (WordZ, rhs) -> rhs
    (lhs, WordZ) -> lhs
    (WordP lhs, WordP rhs) -> do
      let op :: GetWordN mode l -> GetWordN mode r -> GetWordN mode (l + r)
          op = withMode @mode Grisette.sizedBVConcat Grisette.sizedBVConcat
      -- SAFETY: Haskell isn't able to infer that the sum of two positives is
      -- also positive, so we just unsafely get the proof for it.
      case unsafeDict @(1 <= l + r) of
        Dict -> WordP $ op lhs rhs

  sizedBVZext @l @r = \case
    WordZ -> do
      let op :: 1 <= r => GetWordN mode r
          op = withMode @mode
            (Grisette.sizedBVZext @_ @1 Proxy 0)
            (Grisette.sizedBVZext @_ @1 Proxy 0)
      withSizeW op
    WordP value -> do
      let op :: GetWordN mode l -> GetWordN mode r
          op = withMode @mode
            (Grisette.sizedBVZext @_ @l @r Proxy)
            (Grisette.sizedBVZext @_ @l @r Proxy)
      withSizeW $ op value

  sizedBVSext @l @r = \case
    WordZ -> do
      let op :: 1 <= r => GetWordN mode r
          op = withMode @mode
            (Grisette.sizedBVSext @_ @1 Proxy 0)
            (Grisette.sizedBVSext @_ @1 Proxy 0)
      withSizeW op
    WordP value -> do
      let op :: GetWordN mode l -> GetWordN mode r
          op = withMode @mode
            (Grisette.sizedBVSext @_ @l @r Proxy)
            (Grisette.sizedBVSext @_ @l @r Proxy)
      withSizeW $ op value

  sizedBVExt = sizedBVZext

  sizedBVSelect @idx @width @n = \case
    WordZ -> case unsafeDict @(width ~ 0) of
      Dict -> WordZ
    WordP value -> do
      let op :: 1 <= width => GetWordN mode n -> GetWordN mode width
          op = withMode @mode
            (Grisette.sizedBVSelect @_ @n @idx @width Proxy Proxy)
            (Grisette.sizedBVSelect @_ @n @idx @width Proxy Proxy)
      withSizeW $ op value

instance (DecideEvalMode mode, KnownNat n) => GenSym (WordN mode n) (WordN mode n)

instance KnownNat n => GenSym () (WordN S n)

instance GenSymSimple (WordN mode n) (WordN mode n) where
  simpleFresh = pure

instance KnownNat n => GenSymSimple () (WordN S n) where
  simpleFresh spec = withSize @n
    (pure WordZ)
    (WordP <$> simpleFresh spec)

instance KnownNat n => Enum (WordN C n) where
  fromEnum = \case
    WordZ -> 0
    WordP value -> fromEnum value
  toEnum value = withSizeW $ toEnum value

instance KnownNat n => Real (WordN C n) where
  toRational = \case
    WordZ -> 0
    WordP value -> toRational value

instance KnownNat n => Integral (WordN C n) where
  quotRem = \cases
    WordZ WordZ -> raiseDivZero
    (WordP lhs) (WordP rhs) -> bimap WordP WordP $ quotRem lhs rhs

  toInteger = \case
    WordZ -> 0
    WordP value -> toInteger value

instance (DecideEvalMode mode, KnownNat n) => BitCast (IntN mode n) (WordN mode n) where
  bitCast = \case
    IntZ -> WordZ
    IntP value -> do
      let op = withMode @mode bitCast bitCast
      WordP $ op value

instance BitCast (WordN mode n) (WordN mode n) where
  bitCast = id

instance BitCast (WordN S 1) SymBool where
  bitCast (WordP value) = bitCast value

instance BitCast SymBool (WordN S 1) where
  bitCast = WordP . bitCast

instance KnownNat n => IsString (WordN S n) where
  fromString s = withSizeW @n $ fromString s

instance KnownNat n => Solvable (WordN C n) (WordN S n) where
  con = \case
    WordZ -> WordZ
    WordP value -> WordP $ con value

  conView = \case
    WordZ -> pure WordZ
    WordP value -> WordP <$> conView value

  sym symbol = withSizeW @n $ sym symbol

instance (DecideEvalMode mode, KnownNat n) => SignConversion (WordN mode n) (IntN mode n) where
  toSigned = \case
    WordZ -> IntZ
    WordP value -> do
      let op :: GetWordN mode n -> GetIntN mode n
          op = withMode @mode toSigned toSigned
      IntP $ op value

  toUnsigned = \case
    IntZ -> WordZ
    IntP value -> do
      let op :: GetIntN mode n -> GetWordN mode n
          op = withMode @mode toUnsigned toUnsigned
      WordP $ op value
