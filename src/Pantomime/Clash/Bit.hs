{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeOperators #-}

module Symbolic.Clash.Bit
  ( clashInterp
  ) where

import GHC.Plugins
import GHC.Builtin.Types.Prim
import GHC.TypeNats

import Clash.Prelude (Bit, BitVector)
import Clash.Sized.Internal.BitVector
  ( eq##
  , neq##
  , msb#
  , high
  , low
  )

import Grisette.Unified (EvalModeTag (..))
import Grisette

import Control.Monad.Except (MonadError (..))

import Data.Typeable (cast)

import Symbolic.MonadEval
import Symbolic.Value
import Symbolic.WordSize
import Symbolic.Runtime
import Symbolic.Util
import Symbolic.Clash.Util
import Symbolic.Dict
import Symbolic.Sized.BitVector
import Symbolic.Sized.Class

clashInterp
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m [(Var, Value m ws)]
clashInterp = sequence
  [ interpEq
  , interpNeq
  , interpHigh
  , interpLow
  , interpMsb
  ]

bitEquality
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => (WordN' S 1 -> WordN' S 1 -> SymBool)
  -> Type
  -> Value m ws
bitEquality cmp bitTy = Fun bitTy $ \case
  Opaque' _ lhs -> pure . Fun bitTy $ \case
    Opaque' _ rhs -> do
      lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S 1)) lhs
      rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S 1)) rhs

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

interpEq
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpEq = do
  var <- lookupThId 'eq##
  bitTyCon <- lookupThTyCon ''Bit
  let bitTy = mkTyConApp bitTyCon []
  let value = bitEquality (.==) bitTy
  pure (var, value)

interpNeq
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpNeq = do
  var <- lookupThId 'neq##
  bitTyCon <- lookupThTyCon ''Bit
  let bitTy = mkTyConApp bitTyCon []
  let value = bitEquality (./=) bitTy
  pure (var, value)

interpHigh
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpHigh = do
  var <- lookupThId 'high
  bitTyCon <- lookupThTyCon ''Bit
  let bitTy = mkTyConApp bitTyCon []
  let value = highValue bitTy
  pure (var, value)

highValue
  :: forall m ws
   . Type
  -> Value m ws
highValue bitTy = do
  let value :: WordN' S 1
      value = 1
  Opaque' bitTy $ pure value

interpLow
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpLow = do
  var <- lookupThId 'low
  bitTyCon <- lookupThTyCon ''Bit
  let bitTy = mkTyConApp bitTyCon []
  let value = lowValue bitTy
  pure (var, value)

lowValue
  :: forall m ws
   . Type
  -> Value m ws
lowValue bitTy = do
  let value :: WordN' S 1
      value = 0
  Opaque' bitTy $ pure value

interpMsb
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpMsb = do
  var <- lookupThId 'msb#
  bvTyCon <- lookupThTyCon ''BitVector
  bitTyCon <- lookupThTyCon ''Bit
  let bitTy = mkTyConApp bitTyCon []
  let value = msbValue bvTyCon bitTy
  pure (var, value)

msbValue
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => TyCon
  -> Type
  -> Value m ws
msbValue bvTyCon bitTy = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data adt) -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
      Opaque' _ value -> do
        size <- whyFail UnsupportedExpr $ concreteNat adt
        SomeNat @n _ <- pure $ someNatVal size

        value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S n)) value

        SomeNat @idx _ <- pure . someNatVal $ size - 1
        Dict <- pure $ unsafeDict @(idx + 1 <= n)
        let sliced :: RuntimeValue S (WordN' S 1)
            sliced = sizedBVSelect' @_ @idx @1 @n <$> value'

        pure $ Opaque' bitTy sliced
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped
