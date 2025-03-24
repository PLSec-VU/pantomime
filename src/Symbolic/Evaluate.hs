{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Symbolic.Evaluate
  ( evaluate
  , MonadEval
  , SymbolicState (..)
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Core.TyCo.Subst (substTy)
import GHC.Builtin.PrimOps (PrimOp (..))
import GHC.MonadCore

import Control.Monad (forM)
import Control.Monad.Except
import Control.Monad.State

import Data.Functor ((<&>))
import Data.Bits (Bits(..), (.^.))

import Grisette hiding (Rec)
import Grisette.Unified (EvalModeTag (..))

import Symbolic.Util
import Symbolic.WordSize
import Symbolic.Runtime
import Symbolic.ADT
import Symbolic.Value
import Symbolic.Environment

-- TODO: Remove MonadCore from the requirements.
type MonadEval m = (MonadError EvalError m, MonadState SymbolicState m, MonadCore m)

-- | State to track the next unique index for a symbolic identifier.
newtype SymbolicState = SymbolicState
  { nextIdx :: Int
  }

-- | Get a fresh ADT identifier.
freshADT
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => Type
  -> m (ADT S)
freshADT ty = do
  (tyCon, tys) <- whyFail IllTyped $ splitTyConApp_maybe ty

  idx <- state $ \s -> do
    let idx = nextIdx s
    let s' = s { nextIdx = idx + 1 }
    (idx, s')

  -- Create a fresh ADT.
  let symbol = indexed "!ADT" idx
  let adt = pure $ sym symbol

  -- Ensure that the tag is within bounds.
  let adt' = mkADT @ws tyCon tys $ adt

  -- Return fresh ADT and the next index.
  pure adt'

-- | Evaluate an expression into a symbolic Value.
evaluate
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => Environment m ws
  -> CoreExpr
  -> m (Value m ws)
evaluate env = \case
  -- TODO: Add support for CoreUnfolding and DFunUnfolding.
  Var var | Just op <- isPrimOpId_maybe var -> evalPrimOp op
  Var var | Just dataCon <- isDataConId_maybe var -> evalDataCon dataCon
  Var var -> lookupEnv env var

  Lit lit -> evalLiteral lit

  Lam bndr body -> pure . Fun $ \arg -> do
    -- TODO: I think it would be good to have a check here to ensure that the
    -- argument has the correct type.
    env' <- extendEnv env bndr arg
    evaluate env' body

  App fun arg -> do
    fun' <- evaluate env fun
    arg' <- evaluate env arg
    applyValue fun' arg'

  Let (NonRec bndr arg) body -> do
    arg' <- evaluate env arg
    env' <- extendEnv env bndr arg'
    evaluate env' body

  -- Perhaps we could handle these by allowing a Tick annotation to specify an
  -- invariant. Otherwise though, we don't really care about recursive
  -- definitions. I guess bounded recursion would be nice to have, but lets
  -- leave this for now.
  Let (Rec _) _ -> throwError UnsupportedExpr

  Case scrut bndr ty alts -> do
    scrut' <- evaluate env scrut
    env' <- extendEnv env bndr scrut'

    alts' <- forM alts $ evalAlt env' scrut'

    invalid <- invalidValue ty

    foldM' invalid alts' $ \fl (cond, rhs) -> do
      iteValue cond rhs fl

  Cast expr co -> do
    value <- evaluate env expr
    pure $ mkCast' co value

  -- Ticks do not affect evaluation, thus we can skip it.
  Tick _ expr -> evaluate env expr

  Type ty -> do
    let subst = Subst emptyInScopeSet emptyVarEnv (tvSubst env) (cvSubst env)
    let ty' = substTy subst ty
    pure $ Ty ty'

  Coercion co -> do
    let subst = Subst emptyInScopeSet emptyVarEnv (tvSubst env) (cvSubst env)
    let co' = substCo subst co
    pure $ Co co'

-- | Return the condition to run this alternative and its symbolic rhs.
--
-- Expects the case binder to already be bound to the scrutinee in the
-- environment.
evalAlt
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => Environment m ws
  -> Value m ws
  -> CoreAlt
  -> m (RuntimeValue S SymBool, Value m ws)
evalAlt env scrut = \case
  Alt (DataAlt dataCon) bndrs rhs -> do
    -- Ensure the scrutinee is actually an ADT.
    scrut' <- case scrut of
      Data adt -> pure adt
      _ -> throwError IllTyped

    -- Whether the tag of this ADT is equivalent to the DataCon.
    conditional <- whyFail IllTyped $ adtIsDataCon @ws scrut' dataCon

    -- Gather field accessors for all binders.
    -- FIXME: I think the accessor names are returned in the same order as
    -- dataConOrigArgTys. I'm not sure if this actually matches the types we
    -- get here. I think they may be reordered. We should probably use
    -- dataConFieldType_maybe to extract the matching type for each of the
    -- arguments? I'll have to look into this. It's kind of important to not
    -- mess this up!
    let names = dataConAccessorNames dataCon
    let accessors = zip names bndrs
    fields <- forM accessors $ \(name, bndr) -> do
      accessField scrut' name (varType bndr)

    -- Extend the environment with field accessors for each binder.
    env' <- extendManyEnv env $ zip bndrs fields

    -- Evaluate the right-hand side with the extended environment.
    rhs' <- evaluate env' rhs

    -- Return the condition to run this branch and the symbolic right-hand side.
    pure (conditional, rhs')

  Alt (LitAlt lit) [] rhs -> do
    -- Compare the literal, to the scrutinee.
    lit' <- evalLiteral lit
    conditional <- cmpValue scrut lit'

    -- Evaluate the rhs.
    rhs' <- evaluate env rhs

    -- Return the condition to take this branch and the branch itself.
    pure (conditional, rhs')

  Alt DEFAULT [] rhs -> do
    rhs' <- evaluate env rhs
    pure (pure true, rhs')

  _ -> throwError UnsupportedExpr

evalDataCon
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => DataCon
  -> m (Value m ws)
evalDataCon dataCon = do
  -- The root creates the actually symbolic DataCon using the given type
  -- instantiation.
  let root = evalDataConInst dataCon

  -- The number of type arguments we actually require.
  let nUnivTys = const () <$> dataConUnivTyVars dataCon

  -- Create an n-ary function accepting types, which will be used to instantiate
  -- the data constructor.
  final <- nArity root nUnivTys $ \univ _ -> \case
    Ty ty -> pure $ univ <> [ty]
    _ -> throwError IllTyped

  -- We start with an emtpy list of type instances.
  final []

-- | Evaluate a DataCon with the given types as its instantiation.
--
-- This will create a function value with the number of arguments required by
-- the DataCon. The type of these arguments is dictated by the type arguments
-- passed to the function by use of 'dataConInstArgTys'. I.e. the given types
-- should be those applied to the TyCon when constructing the final type.
evalDataConInst
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => DataCon
  -- ^ The DataCon for which we will create a symbolic instance.
  -> [Type]
  -- ^ The types with which we will instantiate universal quantifiers of the
  -- DataCon.
  -> m (Value m ws)
evalDataConInst dataCon tys = do
  -- Create a fresh identifier for the ADT.
  let ty = mkTyConApp (dataConTyCon dataCon) tys
  adt <- freshADT @m @ws ty

  -- Gather the accessor names and instantiate the universal types to create the
  -- field accessors.
  let names = dataConAccessorNames dataCon
  let tys' = scaledThing <$> dataConInstArgTys dataCon tys
  let accessors = zip names tys'

  -- Gather the fields of the ADT.
  fields <- forM accessors $ \(name, fty) -> do
    accessField adt name fty

  -- The root is an ADT that assumes the given conditional holds.
  let root cond = do
        let adt' = assumeADT cond adt
        pure $ Data adt'

  -- Accumulate a function that takes the fields as arguments. We pass a
  -- conditional to the root that states the field accessors are equal to the
  -- actual arguments.
  final <- nArity root fields $ \cond field arg -> do
    -- Constraint the field of the ADT to be equivalent to the argument.
    extra <- cmpValue field arg
    pure $ liftA2 (.&&) extra cond

  -- As a final constraint, the ADT tag should match the given DataCon.
  match <- whyFail IllTyped $ adtIsDataCon @ws adt dataCon
  final match

-- | Get the value corresponding to a literal.
evalLiteral
  :: forall m ws
   . MonadError EvalError m
  => KnownWordSize ws
  => Literal
  -> m (Value m ws)
evalLiteral = fmap Primitive . \case
  LitNumber ty num -> case ty of
    LitNumInt -> pure $ Int num'
    LitNumInt8 -> pure $ Int8 num'
    LitNumInt16 -> pure $ Int16 num'
    LitNumInt32 -> pure $ Int32 num'
    LitNumInt64 -> pure $ Int64 num'
    LitNumWord -> pure $ Word num'
    LitNumWord8 -> pure $ Word8 num'
    LitNumWord16 -> pure $ Word16 num'
    LitNumWord32 -> pure $ Word32 num'
    LitNumWord64 -> pure $ Word64 num'
    -- TODO: The BigNat primitive operations are kind of "hidden". Somehow, we
    -- want to wrap the behaviour!
    -- LitNumBigNat -> throwError ()
    _ -> throwError UnsupportedExpr
    where
      num' :: Num a => RuntimeValue S a
      num' = pure $ fromInteger num

  LitFloat num -> do
    let num' = pure $ fromRational num
    pure $ Float num'

  LitDouble num -> do
    let num' = pure $ fromRational num
    pure $ Double num'

  _ -> throwError UnsupportedExpr

-- | Get the value corresponding to a primitive operation.
-- TODO: I want to add support for rem and quot.
evalPrimOp
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => PrimOp
  -> m (Value m ws)
evalPrimOp = \case
  CharGtOp -> throwError UnsupportedExpr
  CharGeOp -> throwError UnsupportedExpr
  CharEqOp -> throwError UnsupportedExpr
  CharNeOp -> throwError UnsupportedExpr
  CharLtOp -> throwError UnsupportedExpr
  CharLeOp -> throwError UnsupportedExpr
  OrdOp -> throwError UnsupportedExpr
  Int8ToIntOp -> unary $ toIntArch @8
  IntToInt8Op -> unary $ toIntSized @8
  Int8NegOp -> unary $ negate @SymIntN8
  Int8AddOp -> binary $ (+) @SymIntN8
  Int8SubOp -> binary $ (-) @SymIntN8
  Int8MulOp -> binary $ (*) @SymIntN8
  Int8QuotOp -> throwError UnsupportedExpr
  Int8RemOp -> throwError UnsupportedExpr
  Int8QuotRemOp -> throwError UnsupportedExpr
  Int8SllOp -> binary $ symShiftL' @SymIntN8
  Int8SraOp -> binary $ symShiftRA' @SymIntN8
  Int8SrlOp -> binary $ symShiftRL' @SymIntN8
  Int8ToWord8Op -> unary $ toUnsigned @SymWordN8 @SymIntN8
  Int8EqOp -> binary $ symEq @SymIntN8
  Int8GeOp -> binary $ symGe @SymIntN8
  Int8GtOp -> binary $ symGt @SymIntN8
  Int8LeOp -> binary $ symLe @SymIntN8
  Int8LtOp -> binary $ symLt @SymIntN8
  Int8NeOp -> binary $ symNe @SymIntN8
  Word8ToWordOp -> unary $ toWordArch @8
  WordToWord8Op -> unary $ toWordSized @8
  Word8AddOp -> binary $ (+) @SymWordN8
  Word8SubOp -> binary $ (-) @SymWordN8
  Word8MulOp -> binary $ (*) @SymWordN8
  Word8QuotOp -> throwError UnsupportedExpr
  Word8RemOp -> throwError UnsupportedExpr
  Word8QuotRemOp -> throwError UnsupportedExpr
  Word8AndOp -> binary $ (.&.) @SymWordN8
  Word8OrOp -> binary $ (.|.) @SymWordN8
  Word8XorOp -> binary $ (.^.) @SymWordN8
  Word8NotOp -> unary $ complement @SymWordN8
  Word8SllOp -> binary $ symShiftL' @SymWordN8
  Word8SrlOp -> binary $ symShiftRL' @SymWordN8
  Word8ToInt8Op -> unary $ toSigned @SymWordN8 @SymIntN8
  Word8EqOp -> binary $ symEq @SymWordN8
  Word8GeOp -> binary $ symGe @SymWordN8
  Word8GtOp -> binary $ symGt @SymWordN8
  Word8LeOp -> binary $ symLe @SymWordN8
  Word8LtOp -> binary $ symLt @SymWordN8
  Word8NeOp -> binary $ symNe @SymWordN8
  Int16ToIntOp -> unary $ toIntArch @16
  IntToInt16Op -> unary $ toIntSized @16
  Int16NegOp -> unary $ negate @SymIntN16
  Int16AddOp -> binary $ (+) @SymIntN16
  Int16SubOp -> binary $ (-) @SymIntN16
  Int16MulOp -> binary $ (*) @SymIntN16
  Int16QuotOp -> throwError UnsupportedExpr
  Int16RemOp -> throwError UnsupportedExpr
  Int16QuotRemOp -> throwError UnsupportedExpr
  Int16SllOp -> binary $ symShiftL' @SymIntN16
  Int16SraOp -> binary $ symShiftRA' @SymIntN16
  Int16SrlOp -> binary $ symShiftRL' @SymIntN16
  Int16ToWord16Op -> unary $ toUnsigned @SymWordN16 @SymIntN16
  Int16EqOp -> binary $ symEq @SymIntN16
  Int16GeOp -> binary $ symGe @SymIntN16
  Int16GtOp -> binary $ symGt @SymIntN16
  Int16LeOp -> binary $ symLe @SymIntN16
  Int16LtOp -> binary $ symLt @SymIntN16
  Int16NeOp -> binary $ symNe @SymIntN16
  Word16ToWordOp -> unary $ toWordArch @16
  WordToWord16Op -> unary $ toWordSized @16
  Word16AddOp -> binary $ (+) @SymWordN16
  Word16SubOp -> binary $ (-) @SymWordN16
  Word16MulOp -> binary $ (*) @SymWordN16
  Word16QuotOp -> throwError UnsupportedExpr
  Word16RemOp -> throwError UnsupportedExpr
  Word16QuotRemOp -> throwError UnsupportedExpr
  Word16AndOp -> binary $ (.&.) @SymWordN16
  Word16OrOp -> binary $ (.|.) @SymWordN16
  Word16XorOp -> binary $ (.^.) @SymWordN16
  Word16NotOp -> unary $ complement @SymWordN16
  Word16SllOp -> binary $ symShiftL' @SymWordN16
  Word16SrlOp -> binary $ symShiftRL' @SymWordN16
  Word16ToInt16Op -> unary $ toSigned @SymWordN16 @SymIntN16
  Word16EqOp -> binary $ symEq @SymWordN16
  Word16GeOp -> binary $ symGe @SymWordN16
  Word16GtOp -> binary $ symGt @SymWordN16
  Word16LeOp -> binary $ symLe @SymWordN16
  Word16LtOp -> binary $ symLt @SymWordN16
  Word16NeOp -> binary $ symNe @SymWordN16
  Int32ToIntOp -> unary $ toIntArch @32
  IntToInt32Op -> unary $ toIntSized @32
  Int32NegOp -> unary $ negate @SymIntN32
  Int32AddOp -> binary $ (+) @SymIntN32
  Int32SubOp -> binary $ (-) @SymIntN32
  Int32MulOp -> binary $ (*) @SymIntN32
  Int32QuotOp -> throwError UnsupportedExpr
  Int32RemOp -> throwError UnsupportedExpr
  Int32QuotRemOp -> throwError UnsupportedExpr
  Int32SllOp -> binary $ symShiftL' @SymIntN32
  Int32SraOp -> binary $ symShiftRA' @SymIntN32
  Int32SrlOp -> binary $ symShiftRL' @SymIntN32
  Int32ToWord32Op -> unary $ toUnsigned @SymWordN32 @SymIntN32
  Int32EqOp -> binary $ symEq @SymIntN32
  Int32GeOp -> binary $ symGe @SymIntN32
  Int32GtOp -> binary $ symGt @SymIntN32
  Int32LeOp -> binary $ symLe @SymIntN32
  Int32LtOp -> binary $ symLt @SymIntN32
  Int32NeOp -> binary $ symNe @SymIntN32
  Word32ToWordOp -> unary $ toWordArch @32
  WordToWord32Op -> unary $ toWordSized @32
  Word32AddOp -> binary $ (+) @SymWordN32
  Word32SubOp -> binary $ (-) @SymWordN32
  Word32MulOp -> binary $ (*) @SymWordN32
  Word32QuotOp -> throwError UnsupportedExpr
  Word32RemOp -> throwError UnsupportedExpr
  Word32QuotRemOp -> throwError UnsupportedExpr
  Word32AndOp -> binary $ (.&.) @SymWordN32
  Word32OrOp -> binary $ (.|.) @SymWordN32
  Word32XorOp -> binary $ (.^.) @SymWordN32
  Word32NotOp -> unary $ complement @SymWordN32
  Word32SllOp -> binary $ symShiftL' @SymWordN32
  Word32SrlOp -> binary $ symShiftRL' @SymWordN32
  Word32ToInt32Op -> unary $ toSigned @SymWordN32 @SymIntN32
  Word32EqOp -> binary $ symEq @SymWordN32
  Word32GeOp -> binary $ symGe @SymWordN32
  Word32GtOp -> binary $ symGt @SymWordN32
  Word32LeOp -> binary $ symLe @SymWordN32
  Word32LtOp -> binary $ symLt @SymWordN32
  Word32NeOp -> binary $ symNe @SymWordN32
  Int64ToIntOp -> unary $ toIntArch @64
  IntToInt64Op -> unary $ toIntSized @64
  Int64NegOp -> unary $ negate @SymIntN64
  Int64AddOp -> binary $ (+) @SymIntN64
  Int64SubOp -> binary $ (-) @SymIntN64
  Int64MulOp -> binary $ (*) @SymIntN64
  Int64QuotOp -> throwError UnsupportedExpr
  Int64RemOp -> throwError UnsupportedExpr
  Int64SllOp -> binary $ symShiftL' @SymIntN64
  Int64SraOp -> binary $ symShiftRA' @SymIntN64
  Int64SrlOp -> binary $ symShiftRL' @SymIntN64
  Int64ToWord64Op -> unary $ toUnsigned @SymWordN64 @SymIntN64
  Int64EqOp -> binary $ symEq @SymIntN64
  Int64GeOp -> binary $ symGe @SymIntN64
  Int64GtOp -> binary $ symGt @SymIntN64
  Int64LeOp -> binary $ symLe @SymIntN64
  Int64LtOp -> binary $ symLt @SymIntN64
  Int64NeOp -> binary $ symNe @SymIntN64
  Word64ToWordOp -> unary $ toWordArch @64
  WordToWord64Op -> unary $ toWordSized @64
  Word64AddOp -> binary $ (+) @SymWordN64
  Word64SubOp -> binary $ (-) @SymWordN64
  Word64MulOp -> binary $ (*) @SymWordN64
  Word64QuotOp -> throwError UnsupportedExpr
  Word64RemOp -> throwError UnsupportedExpr
  Word64AndOp -> binary $ (.&.) @SymWordN64
  Word64OrOp -> binary $ (.|.) @SymWordN64
  Word64XorOp -> binary $ (.^.) @SymWordN64
  Word64NotOp -> unary $ complement @SymWordN64
  Word64SllOp -> binary $ symShiftL' @SymWordN64
  Word64SrlOp -> binary $ symShiftRL' @SymWordN64
  Word64ToInt64Op -> unary $ toSigned @SymWordN64 @SymIntN64
  Word64EqOp -> binary $ symEq @SymWordN64
  Word64GeOp -> binary $ symGe @SymWordN64
  Word64GtOp -> binary $ symGt @SymWordN64
  Word64LeOp -> binary $ symLe @SymWordN64
  Word64LtOp -> binary $ symLt @SymWordN64
  Word64NeOp -> binary $ symNe @SymWordN64
  IntAddOp -> binary $ (+) @(SymInt ws)
  IntSubOp -> binary $ (-) @(SymInt ws)
  IntMulOp -> binary $ (*) @(SymInt ws)
  IntMul2Op -> throwError UnsupportedExpr
  IntMulMayOfloOp -> throwError UnsupportedExpr
  IntQuotOp -> throwError UnsupportedExpr
  IntRemOp -> throwError UnsupportedExpr
  IntQuotRemOp -> throwError UnsupportedExpr
  IntAndOp -> binary $ (.&.) @(SymInt ws)
  IntOrOp -> binary $ (.|.) @(SymInt ws)
  IntXorOp -> binary $ (.^.) @(SymInt ws)
  IntNotOp -> unary $ complement @(SymInt ws)
  IntNegOp -> unary $ negate @(SymInt ws)
  IntAddCOp -> throwError UnsupportedExpr
  IntSubCOp -> throwError UnsupportedExpr
  IntGtOp -> binary $ symGt @(SymWord ws)
  IntGeOp -> binary $ symGe @(SymWord ws)
  IntEqOp -> binary $ symEq @(SymWord ws)
  IntNeOp -> binary $ symNe @(SymWord ws)
  IntLtOp -> binary $ symLt @(SymWord ws)
  IntLeOp -> binary $ symLe @(SymWord ws)
  ChrOp -> throwError UnsupportedExpr
  IntToWordOp -> unary $ toUnsigned @(SymWord ws) @(SymInt ws)
  IntToFloatOp -> throwError UnsupportedExpr
  IntToDoubleOp -> throwError UnsupportedExpr
  WordToFloatOp -> throwError UnsupportedExpr
  WordToDoubleOp -> throwError UnsupportedExpr
  IntSllOp -> binary $ symShiftL' @(SymInt ws)
  IntSraOp -> binary $ symShiftRA' @(SymInt ws)
  IntSrlOp -> binary $ symShiftRL' @(SymInt ws)
  WordAddOp -> binary $ (+) @(SymWord ws)
  WordAddCOp -> throwError UnsupportedExpr
  WordSubCOp -> throwError UnsupportedExpr
  WordAdd2Op -> throwError UnsupportedExpr
  WordSubOp -> binary $ (-) @(SymWord ws)
  WordMulOp -> binary $ (*) @(SymWord ws)
  WordMul2Op -> throwError UnsupportedExpr
  WordQuotOp -> throwError UnsupportedExpr
  WordRemOp -> throwError UnsupportedExpr
  WordQuotRemOp -> throwError UnsupportedExpr
  WordQuotRem2Op -> throwError UnsupportedExpr
  WordAndOp -> binary $ (.&.) @(SymWord ws)
  WordOrOp -> binary $ (.|.) @(SymWord ws)
  WordXorOp -> binary $ (.^.) @(SymWord ws)
  WordNotOp -> unary $ complement @(SymWord ws)
  WordSllOp -> binary $ symShiftL' @(SymWord ws)
  WordSrlOp -> binary $ symShiftRL' @(SymWord ws)
  WordToIntOp -> unary $ toSigned @(SymWord ws) @(SymInt ws)
  WordGtOp -> binary $ symGt @(SymWord ws)
  WordGeOp -> binary $ symGe @(SymWord ws)
  WordEqOp -> binary $ symEq @(SymWord ws)
  WordNeOp -> binary $ symNe @(SymWord ws)
  WordLtOp -> binary $ symLt @(SymWord ws)
  WordLeOp -> binary $ symLe @(SymWord ws)
  TagToEnumOp -> pure . Fun $ \case
    Ty ty -> pure . Fun $ \case
      Primitive (Int tag) -> do
        adt <- freshADT @m @ws ty

        let conditional = do
              let Tag _ tag' = accessTag @ws adt
              cmpRuntime tag tag'
        -- Assume that the ADT tag matches the given tag. Return the ADT.
        let adt' = assumeADT conditional adt
        pure $ Data adt'
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError UnsupportedExpr
  where
    symShiftRA'
      :: forall bv
       . KnownBitSize bv
      => SymFromIntegral bv (SymIntN (BitSize bv))
      => SymFromIntegral (SymIntN (BitSize bv)) bv
      => bv
      -> SymInt ws
      -> bv
    symShiftRA' = symShiftRA

    symShiftRL'
      :: forall bv
       . KnownBitSize bv
      => SymFromIntegral bv (SymWordN (BitSize bv))
      => SymFromIntegral (SymWordN (BitSize bv)) bv
      => bv
      -> SymInt ws
      -> bv
    symShiftRL' = symShiftRL

    symShiftL'
      :: forall bv
       . SymFromIntegral (SymInt ws) bv
      => SymShift bv
      => bv
      -> SymInt ws
      -> bv
    symShiftL' = symShiftL @bv @ws

    toIntArch :: KnownPos i => SymIntN i -> SymInt ws
    toIntArch = SymInt . sizedBVResize

    toIntSized :: KnownPos i => SymInt ws -> SymIntN i
    toIntSized = sizedBVResize . unSymInt

    toWordArch :: KnownPos i => SymWordN i -> SymWord ws
    toWordArch = SymWord . sizedBVResize

    toWordSized :: KnownPos i => SymWord ws -> SymWordN i
    toWordSized = sizedBVResize . unSymWord

    symGe :: SymOrd a => a -> a -> SymInt ws
    symGe lhs rhs = SymInt $ symIte (lhs .>= rhs) 1 0

    symGt :: SymOrd a => a -> a -> SymInt ws
    symGt lhs rhs = SymInt $ symIte (lhs .> rhs) 1 0

    symEq :: SymEq a => a -> a -> SymInt ws
    symEq lhs rhs = SymInt $ symIte (lhs .== rhs) 1 0

    symNe :: SymEq a => a -> a -> SymInt ws
    symNe lhs rhs = SymInt $ symIte (lhs ./= rhs) 1 0

    symLt :: SymOrd a => a -> a -> SymInt ws
    symLt lhs rhs = SymInt $ symIte (lhs .< rhs) 1 0

    symLe :: SymOrd a => a -> a -> SymInt ws
    symLe lhs rhs = SymInt $ symIte (lhs .<= rhs) 1 0

binary
  :: Wrap m ws (RuntimeValue S a -> RuntimeValue S b -> RuntimeValue S c)
  => (a -> b -> c)
  -> m (Value m ws)
binary = pure . wrap . liftA2 @(RuntimeValue S)

unary
  :: Wrap m ws (RuntimeValue S a -> RuntimeValue S b)
  => (a -> b)
  -> m (Value m ws)
unary = pure . wrap . fmap @(RuntimeValue S)

-- TODO: This wrap stuff is probably better suited in a separate file.
class MonadEval m => Wrap m ws a where
  wrap :: a -> Value m ws

instance MonadEval m => Wrap m ws (RuntimeValue S (SymInt ws)) where
  wrap = Primitive . Int . fmap unSymInt

instance MonadEval m => Wrap m ws (RuntimeValue S SymIntN8) where
  wrap = Primitive . Int8

instance MonadEval m => Wrap m ws (RuntimeValue S SymIntN16) where
  wrap = Primitive . Int16

instance MonadEval m => Wrap m ws (RuntimeValue S SymIntN32) where
  wrap = Primitive . Int32

instance MonadEval m => Wrap m ws (RuntimeValue S SymIntN64) where
  wrap = Primitive . Int64

instance (MonadEval m, KnownWordSize ws) => Wrap m ws (RuntimeValue S (SymWord ws)) where
  wrap = Primitive . Word . fmap unSymWord

instance MonadEval m => Wrap m ws (RuntimeValue S SymWordN8) where
  wrap = Primitive . Word8

instance MonadEval m => Wrap m ws (RuntimeValue S SymWordN16) where
  wrap = Primitive . Word16

instance MonadEval m => Wrap m ws (RuntimeValue S SymWordN32) where
  wrap = Primitive . Word32

instance MonadEval m => Wrap m ws (RuntimeValue S SymWordN64) where
  wrap = Primitive . Word64

instance (MonadEval m, Wrap m ws b) => Wrap m ws (RuntimeValue S (SymInt ws) -> b) where
  wrap f = Fun $ \case
    Primitive (Int arg) -> pure $ wrap @m @ws (f $ arg <&> SymInt)
    _ -> throwError IllTyped

instance (MonadEval m, Wrap m ws b) => Wrap m ws (RuntimeValue S SymIntN8 -> b) where
  wrap f = Fun $ \case
    Primitive (Int8 arg) -> pure $ wrap @m @ws (f arg)
    _ -> throwError IllTyped

instance (MonadEval m, Wrap m ws b) => Wrap m ws (RuntimeValue S SymIntN16 -> b) where
  wrap f = Fun $ \case
    Primitive (Int16 arg) -> pure $ wrap @m @ws (f arg)
    _ -> throwError IllTyped

instance (MonadEval m, Wrap m ws b) => Wrap m ws (RuntimeValue S SymIntN32 -> b) where
  wrap f = Fun $ \case
    Primitive (Int32 arg) -> pure $ wrap @m @ws (f arg)
    _ -> throwError IllTyped

instance (MonadEval m, Wrap m ws b) => Wrap m ws (RuntimeValue S SymIntN64 -> b) where
  wrap f = Fun $ \case
    Primitive (Int64 arg) -> pure $ wrap @m @ws (f arg)
    _ -> throwError IllTyped

instance (MonadEval m, Wrap m ws b) => Wrap m ws (RuntimeValue S (SymWord ws) -> b) where
  wrap f = Fun $ \case
    Primitive (Word arg) -> pure $ wrap @m @ws (f $ arg <&> SymWord)
    _ -> throwError IllTyped

instance (MonadEval m, Wrap m ws b) => Wrap m ws (RuntimeValue S SymWordN8 -> b) where
  wrap f = Fun $ \case
    Primitive (Word8 arg) -> pure $ wrap @m @ws (f arg)
    _ -> throwError IllTyped

instance (MonadEval m, Wrap m ws b) => Wrap m ws (RuntimeValue S SymWordN16 -> b) where
  wrap f = Fun $ \case
    Primitive (Word16 arg) -> pure $ wrap @m @ws (f arg)
    _ -> throwError IllTyped

instance (MonadEval m, Wrap m ws b) => Wrap m ws (RuntimeValue S SymWordN32 -> b) where
  wrap f = Fun $ \case
    Primitive (Word32 arg) -> pure $ wrap @m @ws (f arg)
    _ -> throwError IllTyped

instance (MonadEval m, Wrap m ws b) => Wrap m ws (RuntimeValue S SymWordN64 -> b) where
  wrap f = Fun $ \case
    Primitive (Word64 arg) -> pure $ wrap @m @ws (f arg)
    _ -> throwError IllTyped
