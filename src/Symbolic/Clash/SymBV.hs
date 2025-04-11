{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}

module Symbolic.Clash.SymBV
  ( Signed' (..)
  ) where

import GHC.TypeNats (type (<=), Natural, KnownNat, natVal)

import Grisette hiding (fill)
import Grisette.Unified (EvalModeTag (..), GetIntN)
import qualified Grisette.Unified as Unified

import Data.Bits (Bits (..), FiniteBits (..))
import Data.Data (Proxy(..))

import Symbolic.Dict (withSize)

data Signed' (mode :: EvalModeTag) (n :: Natural) where
  ZSigned :: Signed' mode 0
  PSigned :: 1 <= n => GetIntN mode n -> Signed' mode n

instance (Unified.DecideEvalMode mode, KnownNat n) => Eq (Signed' mode n) where
  (==) = curry $ \case
    (ZSigned, ZSigned) -> true
    (PSigned lhs, PSigned rhs) -> do
      let eq = Unified.withMode @mode (==) (==)
      eq lhs rhs

binary
  :: forall mode n
   . (1 <= n => GetIntN mode n -> GetIntN mode n -> GetIntN mode n)
  -> Signed' mode n
  -> Signed' mode n
  -> Signed' mode n
binary op = curry $ \case
  (ZSigned, ZSigned) -> ZSigned
  (PSigned lhs, PSigned rhs) -> PSigned $ op lhs rhs

unary
  :: forall mode n
   . (1 <= n => GetIntN mode n -> GetIntN mode n)
  -> Signed' mode n
  -> Signed' mode n
unary op = \case
  ZSigned -> ZSigned
  PSigned value -> PSigned $ op value

withSize' :: forall n mode. KnownNat n => (1 <= n => GetIntN mode n) -> Signed' mode n
withSize' value = withSize @n ZSigned (PSigned value)

instance (Unified.DecideEvalMode mode, KnownNat n) => SymEq (Signed' mode n) where
  (.==) = curry $ \case
    (ZSigned, ZSigned) -> true
    (PSigned lhs, PSigned rhs) -> do
      let eq = Unified.withMode @mode (.==) (.==)
      eq lhs rhs

instance (Unified.DecideEvalMode mode, KnownNat n) => SymOrd (Signed' mode n) where
  symCompare = curry $ \case
    (ZSigned, ZSigned) -> pure EQ
    (PSigned lhs, PSigned rhs) -> do
      let cmp = Unified.withMode @mode symCompare symCompare
      cmp lhs rhs

instance (Unified.DecideEvalMode mode, KnownNat n) => Num (Signed' mode n) where
  (+) = binary $ Unified.withMode @mode (+) (+)

  (*) = binary $ Unified.withMode @mode (*) (*)

  abs = unary $ Unified.withMode @mode abs abs

  signum = unary $ Unified.withMode @mode signum signum

  fromInteger value = do
    let op :: 1 <= n => Integer -> GetIntN mode n
        op = Unified.withMode @mode fromInteger fromInteger
    withSize' @n $ op value

  negate = unary $ Unified.withMode @mode negate negate

instance (Unified.DecideEvalMode mode, KnownNat n) => Bits (Signed' mode n) where
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
    ZSigned -> False
    PSigned value' -> do
      let op = Unified.withMode @mode testBit testBit
      op value' idx

  bit idx = do
    let op :: 1 <= n => Int -> GetIntN mode n
        op = Unified.withMode @mode bit bit
    withSize' @n $ op idx

  popCount = \case
    ZSigned -> 0
    PSigned value -> Unified.withMode @mode popCount popCount $ value

instance (Unified.DecideEvalMode mode, KnownNat n) => FiniteBits (Signed' mode n) where
  finiteBitSize _ = fromIntegral (natVal @n Proxy)

instance KnownNat n => ITEOp (Signed' S n) where
  symIte conditional = binary $ symIte conditional

instance KnownNat n => SymFiniteBits (Signed' S n) where
  symTestBit value idx = case value of
    ZSigned -> false
    PSigned value' -> symTestBit value' idx

  symSetBitTo value idx set = case value of
    ZSigned -> ZSigned
    PSigned value' -> PSigned $ symSetBitTo value' idx set

  symFromBits bits = withSize' @n $ symFromBits bits

instance (Unified.DecideEvalMode mode, KnownNat n) => SymShift (Signed' mode n) where
  symShift = binary $ Unified.withMode @mode symShift symShift
  symShiftNegated = binary $ Unified.withMode @mode symShiftNegated symShiftNegated

instance (Unified.DecideEvalMode mode, KnownNat n) => SymRotate (Signed' mode n) where
  symRotate = binary $ Unified.withMode @mode symRotate symRotate
  symRotateNegated = binary $ Unified.withMode @mode symRotateNegated symRotateNegated

instance (Unified.DecideEvalMode mode, KnownNat n) => EvalSym (Signed' mode n) where
  evalSym fill model = do
    let op :: 1 <= n => Bool -> Model -> GetIntN mode n -> GetIntN mode n
        op = Unified.withMode @mode evalSym evalSym
    unary $ op fill model
