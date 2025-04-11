{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeOperators #-}

module Symbolic.Clash.BitVector
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
  , fromInteger#
  , slice#
  , (++#)
  , size#
  )

import GHC.Plugins
import GHC.Builtin.Types.Prim

import GHC.TypeLits
import qualified GHC.TypeNats as TypeNats

import Control.Monad.Except (MonadError(..))

import Data.Bits (Bits (..))
import Data.Coerce (coerce)
import Data.Typeable (cast)

import Grisette.Unified (EvalModeTag (..))
import Grisette

import Symbolic.Value
import Symbolic.MonadEval
import Symbolic.Runtime
import Symbolic.Util
import Symbolic.WordSize
import Symbolic.Dict
import Symbolic.Clash.Util
import Symbolic.Sized.BitVector
import Symbolic.Sized.Class

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
  , interpXToBV
  , interpEq
  , interpNeq
  , interpLt
  , interpLe
  , interpGt
  , interpGe
  , interpFromInteger
  , interpSlice
  , interpConcat
  , interpSize
  ]

-- | Create a type-variable type with the natural kind.
mkNatTyVarTy :: TyVar -> Type
mkNatTyVarTy tyVar = mkTyVarTy $ setVarType tyVar naturalTy

-- | Perform a binary operation on two bit vectors.
--
-- The result value has type:
-- forall n. KnownNat n => BitVector n -> BitVector n -> BitVector n
bvBinary
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => (forall n. KnownNat n => WordN' S n -> WordN' S n -> WordN' S n)
  -> TyCon
  -> Value m ws
-- TODO: It is insanely ugly and error prone to define interpretations like
-- this...
bvBinary op bvTyCon = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data nat) -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
      Opaque' lty lhs -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
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
-- forall n. KnownNat n => BitVector n -> BitVector n
bvUnary
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => (forall n. KnownNat n => WordN' S n -> WordN' S n)
  -> TyCon
  -> Value m ws
bvUnary op bvTyCon = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty sizeTy -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ (Data nat) -> pure . Fun (mkTyConApp bvTyCon [sizeTy]) $ \case
      Opaque' ty value -> do
        size <- whyFail IllTyped $ concreteNat nat
        SomeNat @n _ <- pure $ TypeNats.someNatVal size

        value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S n)) value

        let result = op <$> value'
        pure $ Opaque' ty result

      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped

bvEquality
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => (forall n. KnownNat n => WordN' S n -> WordN' S n -> SymBool)
  -> TyCon
  -> Value m ws
bvEquality cmp bvTyCon = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty size -> pure . Fun cONSTRAINTKind $ \case
    Cast' _ _ -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
      Opaque' _ lhs -> pure . Fun (mkTyConApp bvTyCon [size]) $ \case
        Opaque' _ rhs -> do
          SomeNat @n _ <- whyFail IllTyped $ someTyNat size

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
  _ -> throwError IllTyped

interpAdd
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpAdd = do
  var <- lookupThId '(+#)
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvBinary (+) bvTyCon
  pure (var, value)

interpSub
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpSub = do
  var <- lookupThId '(-#)
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvBinary (-) bvTyCon
  pure (var, value)

interpMul
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpMul = do
  var <- lookupThId '(*#)
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvBinary (*) bvTyCon
  pure (var, value)

interpNeg
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpNeg = do
  var <- lookupThId 'negate#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvUnary negate bvTyCon
  pure (var, value)

interpComplement
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpComplement = do
  var <- lookupThId 'complement#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvUnary complement bvTyCon
  pure (var, value)

interpAnd
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpAnd = do
  var <- lookupThId 'and#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvBinary (.&.) bvTyCon
  pure (var, value)

interpOr
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpOr = do
  var <- lookupThId 'or#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvBinary (.|.) bvTyCon
  pure (var, value)

interpXor
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpXor = do
  var <- lookupThId 'xor#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvBinary xor bvTyCon
  pure (var, value)

interpXToBV
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpXToBV = do
  var <- lookupThId 'xToBV
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvUnary id bvTyCon
  pure (var, value)

interpEq
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpEq = do
  var <- lookupThId 'eq#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvEquality (.==) bvTyCon
  pure (var, value)

interpNeq
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpNeq = do
  var <- lookupThId 'neq#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvEquality (./=) bvTyCon
  pure (var, value)

interpLt
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpLt = do
  var <- lookupThId 'lt#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvEquality (.<) bvTyCon
  pure (var, value)

interpLe
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpLe = do
  var <- lookupThId 'le#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvEquality (.<=) bvTyCon
  pure (var, value)

interpGt
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpGt = do
  var <- lookupThId 'gt#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvEquality (.>) bvTyCon
  pure (var, value)

interpGe
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => KnownWordSize ws
  => m (Var, Value m ws)
interpGe = do
  var <- lookupThId 'ge#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = bvEquality (.>=) bvTyCon
  pure (var, value)

interpFromInteger
  :: forall m ws
   . MonadFail m
  => KnownWordSize ws
  => MonadEval m
  => m (Var, Value m ws)
interpFromInteger = do
  var <- lookupThId 'fromInteger#
  bvTyCon <- lookupThTyCon ''BitVector
  let value = fromIntegerValue bvTyCon
  pure (var, value)

fromIntegerValue
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => TyCon
  -> Value m ws
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
  _ -> throwError IllTyped

interpSlice
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpSlice = do
  var <- lookupThId 'slice#
  bvTyCon <- lookupThTyCon ''BitVector
  snTyCon <- lookupThTyCon ''SNat
  addTyFam <- lookupThTyCon ''(+)
  subTyFam <- lookupThTyCon ''(-)
  let value = sliceValue bvTyCon snTyCon addTyFam subTyFam
  pure (var, value)

sliceValue
  :: forall m ws
   . MonadEval m
  => TyCon
  -> TyCon
  -> TyCon
  -> TyCon
  -> Value m ws
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
                let isNumLitTy' = whyFail UnsupportedExpr . isNumLitTy
                let someNatVal' = whyFail IllTyped . someNatVal
                upper' <- isNumLitTy' upper
                lower' <- isNumLitTy' lower
                top' <- isNumLitTy' top

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

                value' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S n)) value
                let sliced = sizedBVSelect' @_ @idx @w @n <$> value'

                let size' = mkTyConApp subTyFam [upperInc, lower]
                let resTy = mkTyConApp bvTyCon [size']
                pure $ Opaque' resTy sliced

              _ -> throwError IllTyped
            _ -> throwError IllTyped
          _ -> throwError IllTyped
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped

interpConcat
  :: forall m ws
   . MonadFail m
  => MonadEval m
  => m (Var, Value m ws)
interpConcat = do
  var <- lookupThId '(++#)
  bvTyCon <- lookupThTyCon ''BitVector
  addTyFam <- lookupThTyCon ''(+)
  let value = concatValue bvTyCon addTyFam
  pure (var, value)

concatValue
  :: forall m ws
   . MonadEval m
  => TyCon
  -> TyCon
  -> Value m ws
concatValue bvTyCon addTyFam = Fun (mkNatTyVarTy alphaTyVar) $ \case
  Ty rsize -> pure . Fun (mkNatTyVarTy betaTyVar) $ \case
    Ty lsize -> pure . Fun cONSTRAINTKind $ \case
      Cast' _ _ -> pure . Fun (mkTyConApp bvTyCon [lsize]) $ \case
        Opaque' _lty lhs -> pure . Fun (mkTyConApp bvTyCon [rsize]) $ \case
          Opaque' _rty rhs -> do
            SomeNat @l _ <- whyFail IllTyped $ someTyNat lsize
            lhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S l)) lhs

            SomeNat @r _ <- whyFail IllTyped $ someTyNat rsize
            rhs' <- whyFail IllTyped $ cast @_ @(RuntimeValue S (WordN' S r)) rhs

            -- We do this as we need to get the KnownNat constraint on the
            -- output.
            SomeNat @n _ <- whyFail IllTyped $ do
              lsize' <- isNumLitTy lsize
              rsize' <- isNumLitTy rsize
              someNatVal $ lsize' + rsize'
            Dict <- pure $ unsafeDict @(l + r ~ n)

            let concatted :: RuntimeValue S (WordN' S (l + r))
                concatted = liftA2 sizedBVConcat' lhs' rhs'

            let concatted' :: RuntimeValue S (WordN' S n)
                concatted' = coerce concatted

            let size = mkTyConApp addTyFam [lsize, rsize]
            let resTy = mkTyConApp bvTyCon [size]
            pure $ Opaque' resTy concatted'

          _ -> throwError IllTyped
        _ -> throwError IllTyped
      _ -> throwError IllTyped
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
  bvTyCon <- lookupThTyCon ''BitVector
  let value = sizeValue bvTyCon
  pure (var, value)

sizeValue
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => TyCon
  -> Value m ws
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

      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError IllTyped
