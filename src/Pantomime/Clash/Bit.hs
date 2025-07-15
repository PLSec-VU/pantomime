{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeOperators #-}

module Pantomime.Clash.Bit
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
import Grisette (SymBool, SymEq (..), mrgLiftA2, mrgIte)

import Data.Typeable (cast)

import Pantomime.MonadEval
import Pantomime.Value
import Pantomime.WordSize
import Pantomime.Runtime
import Pantomime.Util
import Pantomime.Clash.Util
import Pantomime.Dict
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
  [ interpEq
  , interpNeq
  , interpHigh
  , interpLow
  , interpMsb
  ]

bitEquality
  :: forall es ws
   . Error EvalError :> es
  => KnownWordSize ws
  => (WordN S 1 -> WordN S 1 -> SymBool)
  -> Type
  -> Value (Eff es) ws
bitEquality cmp bitTy = Fun bitTy $ \case
  Opaque' _ lhs -> pure . Fun bitTy $ \case
    Opaque' _ rhs -> do
      lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S 1)) lhs
      rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S 1)) rhs

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
  var <- lookupThId 'eq##
  bitTyCon <- lookupThTyCon ''Bit
  let bitTy = mkTyConApp bitTyCon []
  let value = bitEquality (.==) bitTy
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
  var <- lookupThId 'neq##
  bitTyCon <- lookupThTyCon ''Bit
  let bitTy = mkTyConApp bitTyCon []
  let value = bitEquality (./=) bitTy
  pure (var, value)

interpHigh
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => Eff es (Var, Value (Eff es) ws)
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
  let value :: WordN S 1
      value = 1
  Opaque' bitTy $ pure value

interpLow
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => Eff es (Var, Value (Eff es) ws)
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
  let value :: WordN S 1
      value = 0
  Opaque' bitTy $ pure value

interpMsb
  :: forall es ws
   . Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => KnownWordSize ws
  => Eff es (Var, Value (Eff es) ws)
interpMsb = do
  var <- lookupThId 'msb#
  bvTyCon <- lookupThTyCon ''BitVector
  bitTyCon <- lookupThTyCon ''Bit
  let bitTy = mkTyConApp bitTyCon []
  let value = msbValue bvTyCon bitTy
  pure (var, value)

msbValue
  :: forall es ws
   . Error EvalError :> es
  => KnownWordSize ws
  => TyCon
  -> Type
  -> Value (Eff es) ws
msbValue bvTyCon bitTy = Fun (mkTyVarTy $ setVarType alphaTyVar naturalTy) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data adt) -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
      Opaque' _ value -> do
        size <- whyFail UnsupportedExpr $ concreteNat adt
        SomeNat @n _ <- pure $ someNatVal size

        value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN S n)) value

        SomeNat @idx _ <- pure . someNatVal $ size - 1
        Dict <- pure $ unsafeDict @(idx + 1 <= n)
        let sliced :: RuntimeValue S (WordN S 1)
            sliced = sizedBVSelect @_ @idx @1 @n <$> value'

        pure $ Opaque' bitTy sliced
      _ -> throwError_ IllTyped
    _ -> throwError_ IllTyped
  _ -> throwError_ IllTyped
