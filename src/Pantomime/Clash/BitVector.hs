{-# LANGUAGE MagicHash #-}

module Pantomime.Clash.BitVector
  ( clashInterp
  ) where

import Clash.Prelude (BitVector)
import Clash.Sized.Internal.BitVector
  ( (+#)
  , (-#)
  , (*#)
  , negate#
  , complement#
  , and#
  , or#
  , xor#
  , xToBV
  , eq#
  , neq#
  , lt#
  , le#
  , gt#
  , ge#
  , toInteger#
  , fromInteger#
  , slice#
  , (++#)
  , size#
  , shiftL#
  , shiftR#
  )

import GHC.Plugins
import GHC.Builtin.Types.Prim

import GHC.TypeLits
import GHC.TypeNats qualified as TypeNats

import Control.Monad.Except (MonadError(..))
import Control.Error

import Data.Bits (Bits (complement, xor, (.&.), (.|.)))
import Data.Coerce (coerce)
import Data.Typeable (cast, Proxy (..))

import Grisette.Unified (EvalModeTag (..))
import Grisette
  ( SymBool
  , SymEq (..)
  , SymOrd (..)
  , SymFromIntegral (..)
  , mrgLiftA2
  , mrgIte
  )

import Pantomime.Value
import Pantomime.MonadEval
import Pantomime.Runtime
import Pantomime.Util
import Pantomime.WordSize
import Pantomime.Dict
import Pantomime.Clash.Util
import Pantomime.Grisette.BitVector
import Pantomime.Grisette.SizedBV

import Language.Haskell.TH qualified as TH

import Effectful
import Effectful.Error.Static (Error, throwError_)
import Effectful.GHC.TH
import Effectful.GHC.TyThing

clashInterp
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es [(Var, Value (Eff es) ws)]
clashInterp = sequence
  [ interpAdd
  , interpSub
  , interpMul
  , interpNeg
  , interpComplement
  , interpAnd
  , interpOr
  , interpXor
  , interpXToBV
  , interpEq
  , interpNeq
  , interpLt
  , interpLe
  , interpGt
  , interpGe
  , interpShiftL
  , interpShiftR
  , interpToInteger
  , interpFromInteger
  , interpSlice
  , interpConcat
  , interpSize
  ]

-- | Perform a binary operation on two bit vectors.
--
-- The result value has type:
-- forall n. KnownNat n => BitVector n -> BitVector n -> BitVector n
bvBinary
  :: forall es ws
   . Error EvalError :> es
  => KnownWordSize ws
  => (forall n. KnownNat n => WordN S n -> WordN S n -> WordN S n)
  -> TyCon
  -> Value (Eff es) ws
-- TODO: It is insanely ugly and error prone to define interpretations like
-- this...
bvBinary op bvTyCon = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data nat) -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
      Opaque' lty lhs -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
        Opaque' _rty rhs -> do
          size <- whyFail IllTyped $ concreteNat nat
          SomeNat @n _ <- pure $ TypeNats.someNatVal size

          lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S n)) lhs
          rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S n)) rhs

          let result = mrgLiftA2 op lhs' rhs'
          pure $ Opaque' lty result

        _ -> throwError_ IllTyped
      _ -> throwError_ IllTyped
    _ -> throwError_ IllTyped
  _ -> throwError_ IllTyped

-- | Perform a binary operation on two bit vectors.
--
-- The result value has type:
-- forall n. KnownNat n => BitVector n -> BitVector n
bvUnary
  :: forall es ws
   . Error EvalError :> es
  => KnownWordSize ws
  => (forall n. KnownNat n => WordN S n -> WordN S n)
  -> TyCon
  -> Value (Eff es) ws
bvUnary op bvTyCon = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data nat) -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
      Opaque' ty value -> do
        size <- whyFail IllTyped $ concreteNat nat
        SomeNat @n _ <- pure $ TypeNats.someNatVal size

        value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S n)) value

        let result = op <$> value'
        pure $ Opaque' ty result

      _ -> throwError_ IllTyped
    _ -> throwError_ IllTyped
  _ -> throwError_ IllTyped

bvEquality
  :: forall es ws
   . Error EvalError :> es
  => KnownWordSize ws
  => (forall n. KnownNat n => WordN S n -> WordN S n -> SymBool)
  -> TyCon
  -> Value (Eff es) ws
bvEquality cmp bvTyCon = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data nat) -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
      Opaque' _ lhs -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
        Opaque' _ rhs -> do
          size <- whyFail IllTyped $ concreteNat nat
          SomeNat @n _ <- pure $ TypeNats.someNatVal size

          lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S n)) lhs
          rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S n)) rhs

          let conditional = mrgLiftA2 cmp lhs' rhs'
          let tr = dataConToTag trueDataCon
          let fl = dataConToTag falseDataCon
          let tag = (\c -> mrgIte c tr fl) <$> conditional
          pure $ Data ADT
            { adtTyCon = boolTyCon
            , adtTyArgs = []
            , adtTag = tag
            , adtFields = [[], []]
            }

        _ -> throwError_ IllTyped
      _ -> throwError_ IllTyped
    _ -> throwError_ IllTyped
  _ -> throwError_ IllTyped

bvShift
  :: forall es ws
   . Error EvalError :> es
  => KnownWordSize ws
  => (forall n. KnownNat n => WordN S n -> IntPW S ws -> WordN S n)
  -> TyCon
  -> Value (Eff es) ws
bvShift op bvTyCon = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data nat) -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
      Opaque' ty lhs -> pure . Fun intTy $ \case
        Data adt -> do
          size <- whyFail IllTyped $ concreteNat nat
          SomeNat @n _ <- pure $ TypeNats.someNatVal size

          lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S n)) lhs
          fields <- whyFail IllTyped $ adtDataConFields adt intDataCon
          rhs <- case fields of
            [Primitive (Int rhs)] -> pure $ rhs
            _ -> throwError_ IllTyped

          let result = liftA2 op lhs' rhs
          pure $ Opaque' ty result

        _ -> throwError_ IllTyped
      _ -> throwError_ IllTyped
    _ -> throwError_ IllTyped
  _ -> throwError_ IllTyped

interpAdd
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpAdd = do
  var <- lookupThId '(+#)
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvBinary (+) bvTyCon
  pure (var, value)

interpSub
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpSub = do
  var <- lookupThId '(-#)
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvBinary (-) bvTyCon
  pure (var, value)

interpMul
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpMul = do
  var <- lookupThId '(*#)
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvBinary (*) bvTyCon
  pure (var, value)

interpNeg
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpNeg = do
  var <- lookupThId 'negate#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvUnary negate bvTyCon
  pure (var, value)

interpComplement
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpComplement = do
  var <- lookupThId 'complement#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvUnary complement bvTyCon
  pure (var, value)

interpAnd
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpAnd = do
  var <- lookupThId 'and#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvBinary (.&.) bvTyCon
  pure (var, value)

interpOr
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpOr = do
  var <- lookupThId 'or#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvBinary (.|.) bvTyCon
  pure (var, value)

interpXor
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpXor = do
  var <- lookupThId 'xor#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvBinary xor bvTyCon
  pure (var, value)

interpXToBV
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpXToBV = do
  var <- lookupThId 'xToBV
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvUnary id bvTyCon
  pure (var, value)

interpEq
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpEq = do
  var <- lookupThId 'eq#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvEquality (.==) bvTyCon
  pure (var, value)

interpNeq
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpNeq = do
  var <- lookupThId 'neq#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvEquality (./=) bvTyCon
  pure (var, value)

interpLt
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpLt = do
  var <- lookupThId 'lt#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvEquality (.<) bvTyCon
  pure (var, value)

interpLe
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpLe = do
  var <- lookupThId 'le#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvEquality (.<=) bvTyCon
  pure (var, value)

interpGt
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpGt = do
  var <- lookupThId 'gt#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvEquality (.>) bvTyCon
  pure (var, value)

interpGe
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpGe = do
  var <- lookupThId 'ge#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvEquality (.>=) bvTyCon
  pure (var, value)

interpShiftL
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpShiftL = do
  var <- lookupThId 'shiftL#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvShift shiftL bvTyCon
  pure (var, value)

interpShiftR
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpShiftR = do
  var <- lookupThId 'shiftR#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvShift shiftRL bvTyCon
  pure (var, value)

interpToInteger
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpToInteger = do
  var <- lookupThId 'toInteger#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = toIntegerValue bvTyCon
  pure (var, value)

toIntegerValue
  :: forall es ws
   . Error EvalError :> es
  => KnownWordSize ws
  => TyCon
  -> Value (Eff es) ws
toIntegerValue bvTyCon = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data nat) -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
      Opaque' _ value -> do
        size <- whyFail IllTyped $ concreteNat nat
        SomeNat @n _ <- pure $ TypeNats.someNatVal size

        value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S n)) value


        let wordSize = natVal $ Proxy @(WordBits ws)
        let mask = (2 ^ (wordSize - 1)) - 1

        let tagIS = dataConToTag integerISDataCon
        let tagIP = dataConToTag integerIPDataCon

        let tag = do
              inner <- value'
              let condition = inner .<= mask
              pure $ mrgIte condition tagIS tagIP

        let fieldIS = Primitive . Int $ symFromIntegral <$> value'
        let fieldIP = do
              let bsize = pure $ fromIntegral wordSize
              let array = symFromIntegral <$> value'
              Primitive $ ByteArray bsize array
        let fieldIN = Primitive $ ByteArray (throwError Invalid) (throwError Invalid) 

        pure $ Data ADT
          { adtTyCon = integerTyCon
          , adtTyArgs = []
          , adtTag = tag
          , adtFields =
            [ [fieldIS]
            , [fieldIP]
            , [fieldIN]
            ]
          }

      _ -> throwError_ IllTyped
    _ -> throwError_ IllTyped
  _ -> throwError_ IllTyped

interpFromInteger
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpFromInteger = do
  var <- lookupThId 'fromInteger#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = fromIntegerValue bvTyCon
  pure (var, value)

fromIntegerValue
  :: forall es ws
   . Error EvalError :> es
  => KnownWordSize ws
  => TyCon
  -> Value (Eff es) ws
fromIntegerValue bvTyCon = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data nat) -> pure . Fun naturalTy $ \case
      Data _ -> pure . Fun integerTy $ \case
        Data adt -> do
          size <- whyFail IllTyped $ concreteNat nat
          SomeNat @n _ <- pure $ TypeNats.someNatVal size

          let condIS = adtIsDataCon adt integerISDataCon
          valueIS <- case adtDataConFields adt integerISDataCon of
            Just [Primitive (Int i)] -> pure $ symFromIntegral <$> i
            _ -> throwError_ IllTyped

          let condIP = adtIsDataCon adt integerIPDataCon
          valueIP <- case adtDataConFields adt integerIPDataCon of
            Just [Primitive (ByteArray _ i)] -> pure $ symFromIntegral <$> i
            _ -> throwError_ IllTyped

          let condIN = adtIsDataCon adt integerINDataCon
          valueIN <- case adtDataConFields adt integerINDataCon of
            Just [Primitive (ByteArray _ i)] -> pure $ negate . symFromIntegral <$> i
            _ -> throwError_ IllTyped

          let alts =
                [ (condIS, valueIS)
                , (condIP, valueIP)
                , (condIN, valueIN)
                ]

          let invalid :: RuntimeValue S (WordN S n)
              invalid = throwError Invalid

          let foldl'' acc xs f = foldl' f acc xs

          -- FIXME: This unfolds the prerequisites for the tag multiple times,
          -- potentially bloating the guard.
          let final = foldl'' invalid alts $ \fl (cond, body) -> do
                cond' <- cond
                mrgIte cond' body fl

          let ty = mkTyConApp bvTyCon [sizeTy]
          pure $ Opaque' ty final

        _ -> throwError_ IllTyped
      _ -> throwError_ IllTyped
    _ -> throwError_ IllTyped
  _ -> throwError_ IllTyped

interpSlice
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => Eff es (Var, Value (Eff es) ws)
interpSlice = do
  var <- lookupThId 'slice#
  bvTyCon <- lookupThTyCon ''BitVector
  snTyCon <- lookupThTyCon ''SNat
  addTyFam <- lookupThTyCon ''(+)
  subTyFam <- lookupThTyCon ''(-)
  let value = sliceValue bvTyCon snTyCon addTyFam subTyFam
  pure (var, value)

sliceValue
  :: forall es ws
   . Error EvalError :> es
  => TyCon
  -> TyCon
  -> TyCon
  -> TyCon
  -> Value (Eff es) ws
sliceValue bvTyCon snTyCon addTyFam subTyFam = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty upper -> pure . Fun (mkNatTyVarTy betaTyVar) $ \case
    Ty top -> pure . Fun (mkNatTyVarTy gammaTyVar) $ \case
      Ty lower -> do
        -- Construct the bitvector type.
        let upperInc = mkTyConApp addTyFam [upper, mkNumLitTy 1]
        let size = mkTyConApp addTyFam [upperInc, top]
        let bvTy = mkTyConApp bvTyCon [size]

        pure . Fun bvTy $ \case
          Opaque' _ value -> pure . Fun (mkTyConApp snTyCon [upper]) $ \case
            Data _ -> pure . Fun (mkTyConApp snTyCon [upper]) $ \case
              Data _ -> do
                let normNumLitTy' = whyFail UnsupportedExpr . normNumLitTy
                let someNatVal' = whyFail IllTyped . someNatVal
                upper' <- normNumLitTy' upper
                lower' <- normNumLitTy' lower
                top' <- normNumLitTy' top

                SomeNat @n _ <- someNatVal' $ upper' + 1 + top'
                SomeNat @idx _ <- someNatVal' lower'
                SomeNat @w _ <- someNatVal' $ (upper' + 1) - lower'

                -- Note that this is equal to (idx + n).
                SomeNat @req _ <- someNatVal' $ upper' + 1

                -- The unsafe axiom should be always true since we check it
                -- indirectly via the comparison of req. We cannot compare
                -- directly because (idx + n) is not a KnownNat.
                Dict <- whyFail IllTyped $ leqNat @req @n
                Dict <- pure $ unsafeDict @(idx + w <= n)

                value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S n)) value
                let sliced = sizedBVSelect @_ @idx @w @n <$> value'

                let size' = mkTyConApp subTyFam [upperInc, lower]
                let resTy = mkTyConApp bvTyCon [size']
                pure $ Opaque' resTy sliced

              _ -> throwError_ IllTyped
            _ -> throwError_ IllTyped
          _ -> throwError_ IllTyped
      _ -> throwError_ IllTyped
    _ -> throwError_ IllTyped
  _ -> throwError_ IllTyped

interpConcat
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpConcat = do
  var <- lookupThId '(++#)
  bvTyCon <- lookupThTyCon ''BitVector
  addTyFam <- lookupThTyCon ''(+)
  let value = concatValue bvTyCon addTyFam
  pure (var, value)

concatValue
  :: forall es ws
   . Error EvalError :> es
  => KnownWordSize ws
  => TyCon
  -> TyCon
  -> Value (Eff es) ws
concatValue bvTyCon addTyFam = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty rsizeTy -> pure . Fun (mkNatTyVarTy betaTyVar) $ \case
    Ty lsize -> pure . Fun cONSTRAINTKind $ \case
      Cast' _ (Data nat) -> pure . Fun (mkTyConApp bvTyCon [lsize]) $ \case
        Opaque' _lty lhs -> pure . Fun (mkTyConApp bvTyCon [rsizeTy]) $ \case
          Opaque' _rty rhs -> do
            SomeNat @l _ <- whyFail UnsupportedExpr $ someTyNat lsize
            lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S l)) lhs

            rsize <- whyFail UnsupportedExpr $ concreteNat nat
            SomeNat @r _ <- pure $ TypeNats.someNatVal rsize
            rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S r)) rhs

            -- We do this as we need to get the KnownNat constraint on the
            -- output.
            SomeNat @n _ <- whyFail IllTyped $ do
              lsize' <- normNumLitTy lsize
              someNatVal $ lsize' + toInteger rsize
            Dict <- pure $ unsafeDict @(l + r ~ n)

            let concatted :: RuntimeValue S (WordN S (l + r))
                concatted = liftA2 sizedBVConcat lhs' rhs'

            let concatted' :: RuntimeValue S (WordN S n)
                concatted' = coerce concatted

            let size = mkTyConApp addTyFam [lsize, rsizeTy]
            let resTy = mkTyConApp bvTyCon [size]
            pure $ Opaque' resTy concatted'

          _ -> throwError_ IllTyped
        _ -> throwError_ IllTyped
      _ -> throwError_ IllTyped
    _ -> throwError_ IllTyped
  _ -> throwError_ IllTyped

interpSize
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpSize = do
  var <- lookupThId 'size#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = sizeValue bvTyCon
  pure (var, value)

sizeValue
  :: forall es ws
   . Error EvalError :> es
  => KnownWordSize ws
  => TyCon
  -> Value (Eff es) ws
sizeValue bvTyCon = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data adt) -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
      Opaque' _ _ -> do
        size <- whyFail UnsupportedExpr $ concreteNat adt
        let size' = pure $ fromIntegral size

        pure $ Data ADT
          { adtTyCon = intTyCon
          , adtTyArgs = []
          , adtTag = pure $ dataConToTag intDataCon
          , adtFields = [[Primitive $ Int size']]
          }

      _ -> throwError_ IllTyped
    _ -> throwError_ IllTyped
  _ -> throwError_ IllTyped
