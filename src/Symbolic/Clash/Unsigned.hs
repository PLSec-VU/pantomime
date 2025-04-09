{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
module Symbolic.Clash.Unsigned
  ( clashInterp
  ) where

import Clash.Prelude (Unsigned, BitVector)
import Clash.Sized.Internal.Unsigned ((+#), (-#), (*#), negate#, fromInteger#, unpack#, pack#)

import GHC.Plugins
import GHC.Types.TyThing (lookupId, MonadThings (..))
import GHC.MonadCore
import GHC.TypeLits
import GHC.Builtin.Types.Prim (alphaTyVar)

import Control.Monad.Except (MonadError(..))

import Data.Typeable (cast, Proxy (..))

import Grisette.Unified (EvalModeTag (..))
import Grisette

import Util

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
  , interpFromInteger
  , interpPack#
  , interpUnpack#
  ]

interpAdd
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpAdd = do
  name <- thNameToGhcName' '(+#)
    ??= "Lookup failed."
  var <- liftCore $ lookupId name

  uname <- liftCore $ thNameToGhcName ''Unsigned
  uname' <- whyFail UnsupportedExpr uname
  bvTyCon <- liftCore $ lookupTyCon uname'
  pure (var, addValue bvTyCon)

-- TODO: It is insanely ugly and error prone to define interpretations like
-- this...
addValue
  :: forall m ws
   . MonadEval m
  => TyCon
  -> Value m ws
addValue bvTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
      Opaque' lty lhs -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
        Opaque' _rty rhs -> do
          SomeNat @n _ <- whyFail IllTyped $ do
            size' <- isNumLitTy size
            someNatVal size'

          case cmpNat @1 @n Proxy Proxy of
            LTI -> do
              lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) lhs
              rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) rhs

              let result = mrgLiftA2 (+) lhs' rhs'
              pure $ Opaque' lty result
            _ -> throwError IllTyped
        _ -> throwError IllTyped
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped


interpSub
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpSub = do
  name <- thNameToGhcName' '(-#)
    ??= "Lookup failed."
  var <- liftCore $ lookupId name

  uname <- liftCore $ thNameToGhcName ''Unsigned
  uname' <- whyFail UnsupportedExpr uname
  bvTyCon <- liftCore $ lookupTyCon uname'
  pure (var, subValue bvTyCon)

subValue
  :: forall m ws
   . MonadEval m
  => TyCon
  -> Value m ws
subValue bvTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
      Opaque' lty lhs -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
        Opaque' _rty rhs -> do
          SomeNat @n _ <- whyFail IllTyped $ do
            size' <- isNumLitTy size
            someNatVal size'

          case cmpNat @1 @n Proxy Proxy of
            LTI -> do
              lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) lhs
              rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) rhs

              let result = mrgLiftA2 (-) lhs' rhs'
              pure $ Opaque' lty result
            _ -> throwError IllTyped
        _ -> throwError IllTyped
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped

interpMul
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpMul = do
  name <- thNameToGhcName' '(*#)
    ??= "Lookup failed."
  var <- liftCore $ lookupId name

  uname <- liftCore $ thNameToGhcName ''Unsigned
  uname' <- whyFail UnsupportedExpr uname
  bvTyCon <- liftCore $ lookupTyCon uname'
  pure (var, mulValue bvTyCon)

mulValue
  :: forall m ws
   . MonadEval m
  => TyCon
  -> Value m ws
mulValue bvTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
      Opaque' lty lhs -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
        Opaque' _rty rhs -> do
          SomeNat @n _ <- whyFail IllTyped $ do
            size' <- isNumLitTy size
            someNatVal size'

          case cmpNat @1 @n Proxy Proxy of
            LTI -> do
              lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) lhs
              rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) rhs

              let result = mrgLiftA2 (*) lhs' rhs'
              pure $ Opaque' lty result
            _ -> throwError IllTyped
        _ -> throwError IllTyped
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped

interpNeg
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpNeg = do
  name <- thNameToGhcName' 'negate#
    ??= "Lookup failed."
  var <- liftCore $ lookupId name

  uname <- liftCore $ thNameToGhcName ''Unsigned
  uname' <- whyFail UnsupportedExpr uname
  bvTyCon <- liftCore $ lookupTyCon uname'
  pure (var, negValue bvTyCon)

negValue
  :: forall m ws
   . MonadEval m
  => TyCon
  -> Value m ws
negValue bvTyCon = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
      Opaque' ty value -> do
        SomeNat @n _ <- whyFail IllTyped $ do
          size' <- isNumLitTy size
          someNatVal size'

        case cmpNat @1 @n Proxy Proxy of
          LTI -> do
            value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (SymWordN n)) value

            let result = negate <$> value'
            pure $ Opaque' ty result
          _ -> throwError IllTyped

      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped


interpFromInteger
  :: forall m ws
   . MonadFail m
  => KnownWordSize ws
  => MonadEval m
  => m (Var, Value m ws)
interpFromInteger = do
  name <- thNameToGhcName' 'fromInteger#
    ??= "Lookup failed."
  var <- liftCore $ lookupId name

  uname <- liftCore $ thNameToGhcName ''Unsigned
  uname' <- whyFail UnsupportedExpr uname
  bvTyCon <- liftCore $ lookupTyCon uname'
  pure (var, fromIntegerValue bvTyCon)

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
