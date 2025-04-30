{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
module Pantomime.Clash.Unsigned
  ( clashInterp
  ) where

import Clash.Prelude (Unsigned, BitVector)
import Clash.Sized.Internal.Unsigned
  ( (+#)
  , (-#)
  , (*#)
  , negate#
  , complement#
  , and#
  , or#
  , xor#
  , eq#
  , neq#
  , lt#
  , le#
  , gt#
  , ge#
  , shiftL#
  , shiftR#
  , fromInteger#
  , unpack#
  , pack#
  , size#
  )

import GHC.Plugins
import GHC.Builtin.Types.Prim (alphaTyVar)

import GHC.TypeLits
import qualified GHC.TypeNats as TypeNats

import Control.Monad.Except (MonadError(..))

import Data.Typeable (cast)

import Data.Bits (Bits (..))

import Grisette.Unified (EvalModeTag (..))
import Grisette

import Pantomime.Value
import Pantomime.MonadEval
import Pantomime.Runtime
import Pantomime.Util
import Pantomime.WordSize
import Pantomime.Clash.Util
import Pantomime.Sized.BitVector
import Pantomime.Dict (normNumLitTy)

clashInterp
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m [(Var, Value m ws)]
clashInterp = sequence
  [ interpAdd
  , interpSub
  , interpMul
  , interpNeg
  , interpComplement
  , interpAnd
  , interpOr
  , interpXor
  , interpEq
  , interpNeq
  , interpLt
  , interpLe
  , interpGt
  , interpGe
  , interpShiftL
  , interpShiftR
  , interpFromInteger
  , interpPack#
  , interpUnpack#
  , interpSize
  ]

-- | Perform a binary operation on two Unsigned bit vectors.
--
-- The result value has type:
-- forall n. KnownNat n => Unsigned n -> Unsigned n -> Unsigned n
unBinary
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => (forall n. KnownNat n => WordN' S n -> WordN' S n -> WordN' S n)
  -> TyCon
  -> Value m ws
-- TODO: It is insanely ugly and error prone to define interpretations like
-- this...
unBinary op unTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data nat) -> pure . Fun (mkTyConApp unTyCon [sizeTy]) $ \case
      Opaque' lty lhs -> pure . Fun (mkTyConApp unTyCon [sizeTy]) $ \case
        Opaque' _rty rhs -> do
          size <- whyFail IllTyped $ concreteNat nat
          SomeNat @n _ <- pure $ TypeNats.someNatVal size

          lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S n)) lhs
          rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S n)) rhs

          let result = mrgLiftA2 op lhs' rhs'
          pure $ Opaque' lty result

        _ -> throwError IllTyped
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped

-- | Perform a binary operation on two bit vectors.
--
-- The result value has type:
-- forall n. KnownNat n => Unsigned n -> Unsigned n
unUnary
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => (forall n. KnownNat n => WordN' S n -> WordN' S n)
  -> TyCon
  -> Value m ws
unUnary op unTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data nat) -> pure . Fun (mkTyConApp unTyCon [sizeTy]) $ \case
      Opaque' ty value -> do
        size <- whyFail IllTyped $ concreteNat nat
        SomeNat @n _ <- pure $ TypeNats.someNatVal size

        value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S n)) value

        let result = op <$> value'
        pure $ Opaque' ty result

      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped

unEquality
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => (forall n. KnownNat n => WordN' S n -> WordN' S n -> SymBool)
  -> TyCon
  -> Value m ws
unEquality cmp bvTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
    Opaque' _ lhs -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
      Opaque' _ rhs -> do
        SomeNat @n _ <- whyFail UnsupportedExpr $ do
          size' <- normNumLitTy size
          someNatVal size'

        lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S n)) lhs
        rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S n)) rhs

        let conditional = mrgLiftA2 cmp lhs' rhs'
        let tr = dataConToTag trueDataCon
        let fl = dataConToTag falseDataCon
        let tag = (\c -> symIte c tr fl) <$> conditional
        pure $ Data ADT
          { adtTyCon = boolTyCon
          , adtTyArgs = []
          , adtTag = tag
          , adtFields = [[], []]
          }
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped

unShift
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => (forall n. KnownNat n => WordN' S n -> SymInt ws -> WordN' S n)
  -> TyCon
  -> Value m ws
unShift op bvTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data nat) -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
      Opaque' ty lhs -> pure . Fun intTy $ \case
        Data adt -> do
          size <- whyFail IllTyped $ concreteNat nat
          SomeNat @n _ <- pure $ TypeNats.someNatVal size

          lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S n)) lhs
          fields <- whyFail IllTyped $ adtDataConFields adt intDataCon
          rhs <- case fields of
            [Primitive (Int rhs)] -> pure $ SymInt <$> rhs
            _ -> throwError IllTyped

          let result = liftA2 op lhs' rhs
          pure $ Opaque' ty result

        _ -> throwError IllTyped
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped

interpAdd
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpAdd = do
  var <- lookupThId '(+#)
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unBinary (+) unTyCon
  pure (var, value)

interpSub
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpSub = do
  var <- lookupThId '(-#)
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unBinary (-) unTyCon
  pure (var, value)

interpMul
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpMul = do
  var <- lookupThId '(*#)
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unBinary (*) unTyCon
  pure (var, value)

interpNeg
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpNeg = do
  var <- lookupThId 'negate#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unUnary negate unTyCon
  pure (var, value)

interpComplement
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpComplement = do
  var <- lookupThId 'complement#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unUnary complement unTyCon
  pure (var, value)

interpAnd
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpAnd = do
  var <- lookupThId 'and#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unBinary (.&.) unTyCon
  pure (var, value)

interpOr
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpOr = do
  var <- lookupThId 'or#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unBinary (.|.) unTyCon
  pure (var, value)

interpXor
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpXor = do
  var <- lookupThId 'xor#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unBinary xor unTyCon
  pure (var, value)

interpEq
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpEq = do
  var <- lookupThId 'eq#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unEquality (.==) unTyCon
  pure (var, value)

interpNeq
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpNeq = do
  var <- lookupThId 'neq#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unEquality (./=) unTyCon
  pure (var, value)

interpLt
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpLt = do
  var <- lookupThId 'lt#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unEquality (.<) unTyCon
  pure (var, value)

interpLe
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpLe = do
  var <- lookupThId 'le#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unEquality (.<=) unTyCon
  pure (var, value)

interpGt
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpGt = do
  var <- lookupThId 'gt#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unEquality (.>) unTyCon
  pure (var, value)

interpGe
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpGe = do
  var <- lookupThId 'ge#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unEquality (.>=) unTyCon
  pure (var, value)


interpShiftL
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpShiftL = do
  var <- lookupThId 'shiftL#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = unShift symShiftL' bvTyCon
  pure (var, value)

interpShiftR
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpShiftR = do
  var <- lookupThId 'shiftR#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = unShift symShiftRL' bvTyCon
  pure (var, value)

interpFromInteger
  :: forall m ws
   . MonadFail m
  => KnownWordSize ws
  => MonadEval m
  => m (Var, Value m ws)
interpFromInteger = do
  var <- lookupThId 'fromInteger#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = fromIntegerValue unTyCon
  pure (var, value)

fromIntegerValue
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => TyCon
  -> Value m ws
fromIntegerValue bvTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data nat) ->  pure . Fun integerTy $ \case
      Data adt -> do
        size <- whyFail IllTyped $ concreteNat nat
        SomeNat @n _ <- pure $ TypeNats.someNatVal size

        let condIS = adtIsDataCon adt integerISDataCon
        valueIS <- case adtDataConFields adt integerISDataCon of
          Just [Primitive (Int i)] -> pure $ symFromIntegral <$> i
          _ -> throwError IllTyped

        let condIP = adtIsDataCon adt integerIPDataCon
        valueIP <- case adtDataConFields adt integerIPDataCon of
          Just [Primitive (ByteArray _ i)] -> pure $ symFromIntegral <$> i
          _ -> throwError IllTyped

        let condIN = adtIsDataCon adt integerINDataCon
        valueIN <- case adtDataConFields adt integerINDataCon of
          Just [Primitive (ByteArray _ i)] -> pure $ negate . symFromIntegral <$> i
          _ -> throwError IllTyped

        let alts =
              [ (condIS, valueIS)
              , (condIP, valueIP)
              , (condIN, valueIN)
              ]

        let invalid :: RuntimeValue S (WordN' S n)
            invalid = throwError Invalid

        let foldl'' acc xs f = foldl' f acc xs

        -- FIXME: This unfolds the prerequisites for the tag multiple times,
        -- potentially bloating the guard.
        let final = foldl'' invalid alts $ \fl (cond, body) -> do
              cond' <- cond
              mrgIte cond' body fl

        let ty = mkTyConApp bvTyCon [sizeTy]
        pure $ Opaque' ty final

      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped

interpUnpack#
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpUnpack# = do
  var <- lookupThId 'unpack#
  bvTyCon <- lookupThTyCon ''BitVector
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unpackValue bvTyCon unTyCon
  pure (var, value)

unpackValue
  :: forall m ws
   . MonadEval m
  => TyCon
  -> TyCon
  -> Value m ws
unpackValue bvTyCon unTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
      Opaque' _ value -> do
        pure $ Opaque' (mkTyConApp unTyCon [size]) value
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped

interpPack#
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpPack# = do
  var <- lookupThId 'pack#
  bvTyCon <- lookupThTyCon ''BitVector
  unTyCon <- lookupThTyCon ''Unsigned
  let value = packValue bvTyCon unTyCon
  pure (var, value)

packValue
  :: forall m ws
   . MonadEval m
  => TyCon
  -> TyCon
  -> Value m ws
packValue bvTyCon unTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun (mkTyConApp unTyCon [size]) $ \case
    Opaque' _ value -> do
      pure $ Opaque' (mkTyConApp bvTyCon [size]) value
    _ -> throwError IllTyped
  _ -> throwError IllTyped

interpSize
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpSize = do
  var <- lookupThId 'size#
  bvTyCon <- lookupThTyCon ''Unsigned
  let value = sizeValue bvTyCon
  pure (var, value)

sizeValue
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => TyCon
  -> Value m ws
sizeValue unTyCon = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data adt) -> pure . Fun (mkTyConApp unTyCon [sizeTy]) $ \case
      Opaque' _ _ -> do
        size <- whyFail UnsupportedExpr $ concreteNat adt
        let size' = pure $ fromIntegral size

        pure $ Data ADT
          { adtTyCon = intTyCon
          , adtTyArgs = []
          , adtTag = pure $ dataConToTag intDataCon
          , adtFields = [[Primitive $ Int size']]
          }

      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped
