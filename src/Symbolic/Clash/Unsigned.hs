{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
module Symbolic.Clash.Unsigned
  ( clashInterp
  ) where

import Clash.Prelude (Unsigned, BitVector)
import Clash.Sized.Internal.Unsigned
  ( (+#)
  , (-#)
  , (*#)
  , negate#
  , eq#
  , neq#
  , lt#
  , le#
  , gt#
  , ge#
  , fromInteger#
  , unpack#
  , pack#
  )

import GHC.Plugins
import GHC.TypeLits
import GHC.Builtin.Types.Prim (alphaTyVar)

import Control.Monad.Except (MonadError(..))

import Data.Typeable (cast, Proxy (..))

import Grisette.Unified (EvalModeTag (..))
import Grisette

import Symbolic.Value
import Symbolic.MonadEval
import Symbolic.Runtime
import Symbolic.Util
import Symbolic.WordSize
import Symbolic.Clash.Util

clashInterp
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m [(Var, Value m ws)]
clashInterp = sequence
  [ interpFromInteger
  , interpAdd
  , interpSub
  , interpMul
  , interpNeg
  , interpEq
  , interpNeq
  , interpLt
  , interpLe
  , interpGt
  , interpGe
  , interpFromInteger
  , interpPack#
  , interpUnpack#
  ]

-- | Perform a binary operation on two Unsigned bit vectors.
--
-- The result value has type:
-- forall n. KnownNat n => Unsigned n -> Unsigned n -> Unsigned n
unBinary
  :: forall m ws
   . MonadEval m
  => (forall n. KnownPos n => SymWordN n -> SymWordN n -> SymWordN n)
  -> TyCon
  -> Value m ws
-- TODO: It is insanely ugly and error prone to define interpretations like
-- this...
unBinary op unTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ -> pure . Fun (mkTyConApp unTyCon [size]) $ \case
      Opaque' lty lhs -> pure . Fun (mkTyConApp unTyCon [size]) $ \case
        Opaque' _rty rhs -> do
          SomeNat @n _ <- whyFail IllTyped $ do
            size' <- isNumLitTy size
            someNatVal size'

          case cmpNat @1 @n Proxy Proxy of
            LTI -> do
              lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) lhs
              rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) rhs

              let result = mrgLiftA2 op lhs' rhs'
              pure $ Opaque' lty result
            _ -> throwError IllTyped
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
  => (forall n. KnownPos n => SymWordN n -> SymWordN n)
  -> TyCon
  -> Value m ws
unUnary op unTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ -> pure . Fun (mkTyConApp unTyCon [size]) $ \case
      Opaque' ty value -> do
        SomeNat @n _ <- whyFail IllTyped $ do
          size' <- isNumLitTy size
          someNatVal size'

        case cmpNat @1 @n Proxy Proxy of
          LTI -> do
            value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) value

            let result = op <$> value'
            pure $ Opaque' ty result
          _ -> throwError IllTyped

      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped

unEquality
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => (forall n. KnownPos n => SymWordN n -> SymWordN n -> SymBool)
  -> TyCon
  -> Value m ws
unEquality cmp bvTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
    Opaque' _ lhs -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
      Opaque' _ rhs -> do
        SomeNat @n _ <- whyFail IllTyped $ do
          size' <- isNumLitTy size
          someNatVal size'

        case cmpNat @1 @n Proxy Proxy of
          LTI -> do
            lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) lhs
            rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) rhs

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
  _ -> throwError IllTyped

interpAdd
  :: forall m ws
   . MonadFail m
  => MonadEval m
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
  => m (Var, Value m ws)
interpNeg = do
  var <- lookupThId 'negate#
  unTyCon <- lookupThTyCon ''Unsigned
  let value = unUnary negate unTyCon
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
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ ->  pure . Fun integerTy $ \case
      Data adt -> do
        SomeNat @n _ <- whyFail IllTyped $ do
          size' <- isNumLitTy size
          someNatVal size'

        case cmpNat @1 @n Proxy Proxy of
          LTI -> do
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

            let invalid :: RuntimeValue S (SymWordN n)
                invalid = throwError Invalid

            let foldl'' acc xs f = foldl' f acc xs

            -- FIXME: This unfolds the prerequisites for the tag multiple times,
            -- potentially bloating the guard.
            let final = foldl'' invalid alts $ \fl (cond, body) -> do
                  cond' <- cond
                  mrgIte cond' body fl

            let ty = mkTyConApp bvTyCon [size]
            pure $ Opaque' ty final
          _ -> throwError IllTyped

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
