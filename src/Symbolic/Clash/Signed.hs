{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}

module Symbolic.Clash.Signed
  ( clashInterp
  ) where

import Clash.Prelude (Signed, BitVector)
import Clash.Sized.Internal.Signed ((+#), (-#), (*#), negate#, fromInteger#, unpack#, pack#, abs#)

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
   . MonadEval m
  => MonadFail m
  => KnownWordSize ws
  => m [(Var, Value m ws)]
clashInterp = sequence
  [ interpAdd
  , interpSub
  , interpMul
  , interpNeg
  , interpAbs
  , interpFromInteger
  , interpUnpack#
  , interpPack#
  ]

-- | Perform a binary operation on two Signed bit vectors.
--
-- The result value has type:
-- forall n. KnownNat n => Signed n -> Signed n -> Signed n
siBinary
  :: forall m ws
   . MonadEval m
  => (forall n. KnownPos n => SymIntN n -> SymIntN n -> SymIntN n)
  -> TyCon
  -> Value m ws
-- TODO: It is insanely ugly and error prone to define interpretations like
-- this...
siBinary op siTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ -> pure . Fun (mkTyConApp siTyCon [size]) $ \case
      Opaque' lty lhs -> pure . Fun (mkTyConApp siTyCon [size]) $ \case
        Opaque' _rty rhs -> do
          SomeNat @n _ <- whyFail IllTyped $ do
            size' <- isNumLitTy size
            someNatVal size'

          case cmpNat @1 @n Proxy Proxy of
            LTI -> do
              lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymIntN n)) lhs
              rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymIntN n)) rhs

              let result = mrgLiftA2 op lhs' rhs'
              pure $ Opaque' lty result
            _ -> throwError IllTyped
        _ -> throwError IllTyped
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped

-- | Perform a binary operation on two Signed bit vectors.
--
-- The result value has type:
-- forall n. KnownNat n => Signed n -> Signed n
siUnary
  :: forall m ws
   . MonadEval m
  => (forall n. KnownPos n => SymIntN n -> SymIntN n)
  -> TyCon
  -> Value m ws
siUnary op siTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ -> pure . Fun (mkTyConApp siTyCon [size]) $ \case
      Opaque' ty value -> do
        SomeNat @n _ <- whyFail IllTyped $ do
          size' <- isNumLitTy size
          someNatVal size'

        case cmpNat @1 @n Proxy Proxy of
          LTI -> do
            value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymIntN n)) value

            let result = op <$> value'
            pure $ Opaque' ty result
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
  siTyCon <- lookupThTyCon ''Signed
  let value = siBinary (+) siTyCon
  pure (var, value)

interpSub
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpSub = do
  var <- lookupThId '(-#)
  siTyCon <- lookupThTyCon ''Signed
  let value = siBinary (-) siTyCon
  pure (var, value)

interpMul
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpMul = do
  var <- lookupThId '(*#)
  siTyCon <- lookupThTyCon ''Signed
  let value = siBinary (*) siTyCon
  pure (var, value)

interpNeg
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpNeg = do
  var <- lookupThId 'negate#
  siTyCon <- lookupThTyCon ''Signed
  let value = siUnary negate siTyCon
  pure (var, value)

interpAbs
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpAbs = do
  var <- lookupThId 'abs#
  siTyCon <- lookupThTyCon ''Signed
  let value = siUnary abs siTyCon
  pure (var, value)

interpFromInteger
  :: forall m ws
   . MonadFail m
  => KnownWordSize ws
  => MonadEval m
  => m (Var, Value m ws)
interpFromInteger = do
  var <- lookupThId 'fromInteger#
  siTyCon <- lookupThTyCon ''Signed
  let value = fromIntegerValue siTyCon
  pure (var, value)

fromIntegerValue
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => TyCon
  -> Value m ws
fromIntegerValue siTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
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

            let invalid :: RuntimeValue S (SymIntN n)
                invalid = throwError Invalid

            let foldl'' acc xs f = foldl' f acc xs

            -- FIXME: This unfolds the prerequisites for the tag multiple times,
            -- potentially bloating the guard.
            let final = foldl'' invalid alts $ \fl (cond, body) -> do
                  cond' <- cond
                  mrgIte cond' body fl

            let ty = mkTyConApp siTyCon [size]
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
  unTyCon <- lookupThTyCon ''Signed
  let value = unpackValue bvTyCon unTyCon
  pure (var, value)

unpackValue
  :: forall m ws
   . MonadEval m
  => TyCon
  -> TyCon
  -> Value m ws
unpackValue bvTyCon siTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
      Opaque' _ value -> do
        SomeNat @n _ <- whyFail IllTyped $ do
          size' <- isNumLitTy size
          someNatVal size'

        case cmpNat @1 @n Proxy Proxy of
          LTI -> do
            value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) value

            let ty = mkTyConApp siTyCon [size]
            let result = toSigned <$> value'
            pure $ Opaque' ty result
          _ -> throwError IllTyped
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
  unTyCon <- lookupThTyCon ''Signed
  let value = packValue bvTyCon unTyCon
  pure (var, value)

packValue
  :: forall m ws
   . MonadEval m
  => TyCon
  -> TyCon
  -> Value m ws
packValue bvTyCon siTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ -> pure . Fun (mkTyConApp siTyCon [size]) $ \case
      Opaque' _ value -> do
        SomeNat @n _ <- whyFail IllTyped $ do
          size' <- isNumLitTy size
          someNatVal size'

        case cmpNat @1 @n Proxy Proxy of
          LTI -> do
            value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymIntN n)) value

            let ty = mkTyConApp bvTyCon [size]
            let result = toUnsigned <$> value'
            pure $ Opaque' ty result
          _ -> throwError IllTyped
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped
