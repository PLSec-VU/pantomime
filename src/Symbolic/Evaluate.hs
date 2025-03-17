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
  , SymbolicState (..)
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Map.Expr (TrieMap(..), insertTM)
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Types.Unique.DFM (UniqDFM)
import GHC.Builtin.PrimOps (PrimOp (..))
import GHC.MonadCore

import Control.Monad (forM)
import Control.Monad.Except
import Control.Monad.State

import Data.Functor ((<&>))
import Data.Bits (Bits(..), (.^.))

-- TODO: There has to be a better way to not import pretty printing stuff from
-- grisette...
import Grisette hiding (PPrintType (..), (<>), (<+>), nest, punctuate, comma, vcat, braces, lbrace, rbrace)

import Symbolic.Util
import Symbolic.KnownPos
import Symbolic.Runtime
import Symbolic.ADT
import Symbolic.Value
import BitVec

type MonadSymbolic m = (MonadError SymbolicError m, MonadState SymbolicState m, MonadCore m)

newtype SymbolicState = SymbolicState
  { nextIdx :: Int
  }

freshADT :: MonadState SymbolicState m => m (RuntimeValue SymADT)
freshADT = state $ \s -> do
  let idx = nextIdx s
  let s' = s { nextIdx = idx + 1 }
  let adt = sym $ indexed "!ADT" idx
  (pure adt, s')

type Environment m n = UniqDFM Var (Value m n)

evaluate
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => Environment m n
  -> CoreExpr
  -> m (Value m n)
evaluate env = \case
  -- TODO: Add support for CoreUnfolding and DFunUnfolding.
  Var var | Just op <- isPrimOpId_maybe var -> evalPrimOp op
  Var var | Just dataCon <- isDataConId_maybe var -> evalDataCon dataCon
  Var var -> whyFail UnboundVariable $ lookupTM var env

  Lit lit -> evalLiteral lit

  Lam bndr body -> pure . Fun $ \arg -> do
    -- TODO: I think it would be good to have a check here to ensure that the
    -- argument has the correct type.
    let env' = insertTM bndr arg env
    evaluate env' body

  App fun arg -> do
    fun' <- evaluate env fun
    arg' <- evaluate env arg
    applyValue fun' arg'

  Let (NonRec bndr arg) body -> do
    arg' <- evaluate env arg
    let env' = insertTM bndr arg' env
    evaluate env' body

  -- Perhaps we could handle these by allowing a Tick annotation to specify an
  -- invariant. Otherwise though, we don't really care about recursive
  -- definitions. I guess bounded recursion would be nice to have, but lets
  -- leave this for now.
  Let (Rec _) _ -> throwError UnsupportedExpr

  Case scrut bndr ty alts -> do
    scrut' <- evaluate env scrut
    let env' = insertTM bndr scrut' env

    alts' <- forM alts $ evalAlt env' scrut'

    invalid <- invalidValue ty

    foldM' invalid alts' $ \fl (cond, rhs) -> do
      iteValue cond rhs fl

  Cast expr co -> do
    value <- evaluate env expr
    pure $ mkCast' co value

  -- Ticks do not affect evaluation, thus we can skip it.
  Tick _ expr -> evaluate env expr

  -- FIXME: I should substitute the type.
  Type ty -> pure $ Ty ty

  -- FIXME: I should substitute the coercion.
  Coercion co -> pure $ Co co

-- | Return the condition to run this alternative and its symbolic rhs.
--
-- Expects the case binder to already be bound to the scrutinee in the
-- environment.
evalAlt
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => Environment m n
  -> Value m n
  -> CoreAlt
  -> m (RuntimeValue SymBool, Value m n)
evalAlt env scrut = \case
  Alt (DataAlt dataCon) bndrs rhs -> do
    -- Ensure the scrutinee is actually an ADT.
    scrut' <- case scrut of
      ADT _ adt -> pure adt
      _ -> throwError IllTyped

    -- Whether the "tag" field on this ADT is equivalent to the DataCon.
    let conditional = adtIsDataCon @n scrut' dataCon

    -- Gather field accessors for all binders.
    let names = dataConAccessorNames dataCon
    let accessors = zip names bndrs
    fields <- forM accessors $ \(name, bndr) -> do
      accessField' scrut' name (varType bndr)

    -- Extend the environment with field accessors for each binder.
    let insertManyTM = foldl' . flip . uncurry $ insertTM
    let env' = insertManyTM env $ zip bndrs fields

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
    let conditional = case scrut of
          ADT ty adt -> do
            -- Ensure that the tag is at least in range.
            -- TODO: Should this not be a prerequisite for any ADT? I.e. that
            -- whenever we create a symbolic ADT value this should be already
            -- constrained? Not sure which is better, so I'll leave it here for
            -- now.
            let (tyCon, _) = splitTyConApp ty
            let amount = length $ tyConDataCons tyCon
            tag <- accessTag @n adt
            mrgReturn $ 0 .<= tag .&& tag .< fromIntegral amount
          _ -> pure true
            
    rhs' <- evaluate env rhs
    pure (conditional, rhs')

  _ -> throwError UnsupportedExpr

evalDataCon
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => DataCon
  -> m (Value m n)
evalDataCon dataCon = do
  -- The root creates the actually symbolic DataCon using the given type
  -- instantiation.
  let root = evalDataConInst dataCon

  -- The number of type arguments we actually require.
  let nUnivTys = const () <$> dataConUnivTyVars dataCon

  -- Create an n-ary function accepting types, which will be used to instantiate
  -- the data constructor.
  final <- nArity root nUnivTys $ \_ univ -> \case
    Ty ty -> pure $ ty : univ
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
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => DataCon
  -- ^ The DataCon for which we will create a symbolic instance.
  -> [Type]
  -- ^ The types with which we will instantiate universal quantifiers of the
  -- DataCon.
  -> m (Value m n)
evalDataConInst dataCon tys = do
  -- Create a fresh identifier for the ADT.
  adt <- freshADT

  -- Gather the accessor names and instantiate the universal types to create the
  -- field accessors.
  let names = dataConAccessorNames dataCon
  let tys' = scaledThing <$> dataConInstArgTys dataCon tys
  let accessors = zip names tys'

  -- Gather the fields of the ADT.
  fields <- forM accessors $ \(name, ty) -> do
    accessField' adt name ty

  -- The root is an ADT that asserts the given conditional holds.
  let root cond = do
        let ty = mkTyConApp (dataConTyCon dataCon) tys
        let value = assertRuntime cond adt
        pure $ ADT ty value

  -- Accumulate a function that takes the fields as arguments. We pass a
  -- conditional to the root that states the field accessors are equal to the
  -- actual arguments.
  final <- nArity root fields $ \field cond arg -> do
    -- Constraint the field of the ADT to be equivalent to the argument.
    extra <- cmpValue field arg
    pure $ liftA2 (.&&) extra cond

  -- As a final constraint, the ADT tag should match the given DataCon.
  final $ adtIsDataCon @n adt dataCon

-- | Get the dynamically typed, symbolic function for a primitive operation.
-- TODO: I want to add support for rem and quot.
evalPrimOp
  :: forall m n
   . MonadSymbolic m
  => KnownPos n
  => PrimOp
  -> m (Value m n)
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
  Int8SllOp -> binary $ symShiftL' @SymIntN @8
  Int8SraOp -> binary $ symShiftRA' @SymIntN @8
  Int8SrlOp -> binary $ symShiftRL' @SymIntN @8
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
  Word8SllOp -> binary $ symShiftL' @SymWordN @8
  Word8SrlOp -> binary $ symShiftRL' @SymWordN @8
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
  Int16SllOp -> binary $ symShiftL' @SymIntN @16
  Int16SraOp -> binary $ symShiftRA' @SymIntN @16
  Int16SrlOp -> binary $ symShiftRL' @SymIntN @16
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
  Word16SllOp -> binary $ symShiftL' @SymWordN @16
  Word16SrlOp -> binary $ symShiftRL' @SymWordN @16
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
  Int32SllOp -> binary $ symShiftL' @SymIntN @32
  Int32SraOp -> binary $ symShiftRA' @SymIntN @32
  Int32SrlOp -> binary $ symShiftRL' @SymIntN @32
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
  Word32SllOp -> binary $ symShiftL' @SymWordN @32
  Word32SrlOp -> binary $ symShiftRL' @SymWordN @32
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
  Int64SllOp -> binary $ symShiftL' @SymIntN @64
  Int64SraOp -> binary $ symShiftRA' @SymIntN @64
  Int64SrlOp -> binary $ symShiftRL' @SymIntN @64
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
  Word64SllOp -> binary $ symShiftL' @SymWordN @64
  Word64SrlOp -> binary $ symShiftRL' @SymWordN @64
  Word64ToInt64Op -> unary $ toSigned @SymWordN64 @SymIntN64
  Word64EqOp -> binary $ symEq @SymWordN64
  Word64GeOp -> binary $ symGe @SymWordN64
  Word64GtOp -> binary $ symGt @SymWordN64
  Word64LeOp -> binary $ symLe @SymWordN64
  Word64LtOp -> binary $ symLt @SymWordN64
  Word64NeOp -> binary $ symNe @SymWordN64
  IntAddOp -> binary $ (+) @(SymIntArch n)
  IntSubOp -> binary $ (-) @(SymIntArch n)
  IntMulOp -> binary $ (*) @(SymIntArch n)
  IntMul2Op -> throwError UnsupportedExpr
  IntMulMayOfloOp -> throwError UnsupportedExpr
  IntQuotOp -> throwError UnsupportedExpr
  IntRemOp -> throwError UnsupportedExpr
  IntQuotRemOp -> throwError UnsupportedExpr
  IntAndOp -> binary $ (.&.) @(SymIntArch n)
  IntOrOp -> binary $ (.|.) @(SymIntArch n)
  IntXorOp -> binary $ (.^.) @(SymIntArch n)
  IntNotOp -> unary $ complement @(SymIntArch n)
  IntNegOp -> unary $ negate @(SymIntArch n)
  IntAddCOp -> throwError UnsupportedExpr
  IntSubCOp -> throwError UnsupportedExpr
  IntGtOp -> binary $ symGt @(SymWordArch n)
  IntGeOp -> binary $ symGe @(SymWordArch n)
  IntEqOp -> binary $ symEq @(SymWordArch n)
  IntNeOp -> binary $ symNe @(SymWordArch n)
  IntLtOp -> binary $ symLt @(SymWordArch n)
  IntLeOp -> binary $ symLe @(SymWordArch n)
  ChrOp -> throwError UnsupportedExpr
  IntToWordOp -> unary $ toUnsigned @(SymWordArch n) @(SymIntArch n)
  IntToFloatOp -> throwError UnsupportedExpr
  IntToDoubleOp -> throwError UnsupportedExpr
  WordToFloatOp -> throwError UnsupportedExpr
  WordToDoubleOp -> throwError UnsupportedExpr
  IntSllOp -> binary $ symShiftL' @SymIntArch @n
  IntSraOp -> binary $ symShiftRA' @SymIntArch @n
  IntSrlOp -> binary $ symShiftRL' @SymIntArch @n
  WordAddOp -> binary $ (+) @(SymWordArch n)
  WordAddCOp -> throwError UnsupportedExpr
  WordSubCOp -> throwError UnsupportedExpr
  WordAdd2Op -> throwError UnsupportedExpr
  WordSubOp -> binary $ (-) @(SymWordArch n)
  WordMulOp -> binary $ (*) @(SymWordArch n)
  WordMul2Op -> throwError UnsupportedExpr
  WordQuotOp -> throwError UnsupportedExpr
  WordRemOp -> throwError UnsupportedExpr
  WordQuotRemOp -> throwError UnsupportedExpr
  WordQuotRem2Op -> throwError UnsupportedExpr
  WordAndOp -> binary $ (.&.) @(SymWordArch n)
  WordOrOp -> binary $ (.|.) @(SymWordArch n)
  WordXorOp -> binary $ (.^.) @(SymWordArch n)
  WordNotOp -> unary $ complement @(SymWordArch n)
  WordSllOp -> binary $ symShiftL' @SymWordArch @n
  WordSrlOp -> binary $ symShiftRL' @SymWordArch @n
  WordToIntOp -> unary $ toSigned @(SymWordArch n) @(SymIntArch n)
  WordGtOp -> binary $ symGt @(SymWordArch n)
  WordGeOp -> binary $ symGe @(SymWordArch n)
  WordEqOp -> binary $ symEq @(SymWordArch n)
  WordNeOp -> binary $ symNe @(SymWordArch n)
  WordLtOp -> binary $ symLt @(SymWordArch n)
  WordLeOp -> binary $ symLe @(SymWordArch n)
  TagToEnumOp -> pure . Fun $ \case
    Ty ty -> pure . Fun $ \case
      Int tag -> do
        adt <- freshADT
        let cond = cmpRuntime tag $ accessTag @n adt
        pure . ADT ty $ assertRuntime cond adt
      _ -> throwError IllTyped
    _ -> throwError IllTyped
  _ -> throwError UnsupportedExpr
  where
    symShiftRL'
      :: forall bv i
       . SymFromIntegral (SymWordN i) (bv i)
      => SymFromIntegral (bv i) (SymWordN i)
      => KnownPos i
      => bv i
      -> SymIntArch n
      -> bv i
    symShiftRL' lhs rhs = symShiftRL lhs $ unSymIntArch rhs

    symShiftRA'
      :: forall bv i
       . SymFromIntegral (SymIntN i) (bv i)
      => SymFromIntegral (bv i) (SymIntN i)
      => KnownPos i
      => bv i
      -> SymIntArch n
      -> bv i
    symShiftRA' lhs rhs = symShiftRA lhs $ unSymIntArch rhs

    symShiftL'
      :: forall bv i
       . SymFromIntegral (SymIntN i) (bv i)
      => SymShift (bv i)
      => KnownPos i
      => bv i
      -> SymIntArch n
      -> bv i
    symShiftL' lhs rhs = symShiftL lhs $ unSymIntArch rhs

    toIntArch :: KnownPos i => SymIntN i -> SymIntArch n
    toIntArch = SymIntArch . sizedBVResize

    toIntSized :: KnownPos i => SymIntArch n -> SymIntN i
    toIntSized = sizedBVResize . unSymIntArch

    toWordArch :: KnownPos i => SymWordN i -> SymWordArch n
    toWordArch = SymWordArch . sizedBVResize

    toWordSized :: KnownPos i => SymWordArch n -> SymWordN i
    toWordSized = sizedBVResize . unSymWordArch

    symGe :: SymOrd a => a -> a -> SymIntArch n
    symGe lhs rhs = SymIntArch $ symIte (lhs .>= rhs) 1 0

    symGt :: SymOrd a => a -> a -> SymIntArch n
    symGt lhs rhs = SymIntArch $ symIte (lhs .> rhs) 1 0

    symEq :: SymEq a => a -> a -> SymIntArch n
    symEq lhs rhs = SymIntArch $ symIte (lhs .== rhs) 1 0

    symNe :: SymEq a => a -> a -> SymIntArch n
    symNe lhs rhs = SymIntArch $ symIte (lhs ./= rhs) 1 0

    symLt :: SymOrd a => a -> a -> SymIntArch n
    symLt lhs rhs = SymIntArch $ symIte (lhs .< rhs) 1 0

    symLe :: SymOrd a => a -> a -> SymIntArch n
    symLe lhs rhs = SymIntArch $ symIte (lhs .<= rhs) 1 0

binary
  :: Wrap m n (RuntimeValue a -> RuntimeValue b -> RuntimeValue c)
  => (a -> b -> c)
  -> m (Value m n)
binary = pure . wrap . liftA2 @(ExceptT RuntimeError Union)

unary
  :: Wrap m n (RuntimeValue a -> RuntimeValue b)
  => (a -> b)
  -> m (Value m n)
unary = pure . wrap . fmap @(ExceptT RuntimeError Union)

-- TODO: This stuff is probably better suited in a separate file.
class MonadSymbolic m => Wrap m n a where
  wrap :: a -> Value m n

newtype SymIntArch n where
  SymIntArch :: SymIntN n -> SymIntArch n

unSymIntArch :: SymIntArch n -> SymIntN n
unSymIntArch (SymIntArch val) = val

deriving via SymIntN n instance KnownPos n => Num (SymIntArch n)
deriving via SymIntN n instance KnownPos n => Eq (SymIntArch n)
deriving via SymIntN n instance KnownPos n => Bits (SymIntArch n)
deriving via SymIntN n instance KnownPos n => SymOrd (SymIntArch n)
deriving via SymIntN n instance KnownPos n => SymEq (SymIntArch n)
deriving via SymIntN n instance KnownPos n => SymShift (SymIntArch n)
deriving via SymIntN n instance KnownPos n => SymFromIntegral (SymIntN n) (SymIntArch n)
deriving via SymIntN n instance KnownPos n => SymFromIntegral (SymWordN n) (SymIntArch n)
deriving via SymIntN n instance KnownPos n => SymFromIntegral (SymIntArch n) (SymIntN n)
deriving via SymIntN n instance KnownPos n => SymFromIntegral (SymWordArch n) (SymIntN n)

newtype SymWordArch n where
  SymWordArch :: SymWordN n -> SymWordArch n

unSymWordArch :: SymWordArch n -> SymWordN n
unSymWordArch (SymWordArch val) = val

deriving via SymWordN n instance KnownPos n => Num (SymWordArch n)
deriving via SymWordN n instance KnownPos n => Eq (SymWordArch n)
deriving via SymWordN n instance KnownPos n => Bits (SymWordArch n)
deriving via SymWordN n instance KnownPos n => SymOrd (SymWordArch n)
deriving via SymWordN n instance KnownPos n => SymEq (SymWordArch n)
deriving via SymWordN n instance KnownPos n => SymShift (SymWordArch n)
deriving via SymWordN n instance KnownPos n => SymFromIntegral (SymIntN n) (SymWordArch n)
deriving via SymWordN n instance KnownPos n => SymFromIntegral (SymWordN n) (SymWordArch n)
deriving via SymWordN n instance KnownPos n => SymFromIntegral (SymWordArch n) (SymWordN n)
deriving via SymWordN n instance KnownPos n => SymFromIntegral (SymIntArch n) (SymWordN n)

instance KnownPos n => SignConversion (SymWordArch n) (SymIntArch n) where
  toUnsigned = SymWordArch . toUnsigned . unSymIntArch
  toSigned = SymIntArch . toSigned . unSymWordArch

instance (MonadSymbolic m, KnownPos n) => Wrap m n (RuntimeValue (SymIntArch n)) where
  wrap = Int . fmap unSymIntArch

instance MonadSymbolic m => Wrap m n (RuntimeValue SymIntN8) where
  wrap = Int8

instance MonadSymbolic m => Wrap m n (RuntimeValue SymIntN16) where
  wrap = Int16

instance MonadSymbolic m => Wrap m n (RuntimeValue SymIntN32) where
  wrap = Int32

instance MonadSymbolic m => Wrap m n (RuntimeValue SymIntN64) where
  wrap = Int64

instance (MonadSymbolic m, KnownPos n) => Wrap m n (RuntimeValue (SymWordArch n)) where
  wrap = Word . fmap unSymWordArch

instance MonadSymbolic m => Wrap m n (RuntimeValue SymWordN8) where
  wrap = Word8

instance MonadSymbolic m => Wrap m n (RuntimeValue SymWordN16) where
  wrap = Word16

instance MonadSymbolic m => Wrap m n (RuntimeValue SymWordN32) where
  wrap = Word32

instance MonadSymbolic m => Wrap m n (RuntimeValue SymWordN64) where
  wrap = Word64

instance (MonadSymbolic m, KnownPos n, Wrap m n b) => Wrap m n (RuntimeValue (SymIntArch n) -> b) where
  wrap f = Fun $ \case
    Int arg -> pure $ wrap @m @n (f $ arg <&> SymIntArch)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymIntN8 -> b) where
  wrap f = Fun $ \case
    Int8 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymIntN16 -> b) where
  wrap f = Fun $ \case
    Int16 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymIntN32 -> b) where
  wrap f = Fun $ \case
    Int32 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymIntN64 -> b) where
  wrap f = Fun $ \case
    Int64 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, KnownPos n, Wrap m n b) => Wrap m n (RuntimeValue (SymWordArch n) -> b) where
  wrap f = Fun $ \case
    Word arg -> pure $ wrap @m @n (f $ arg <&> SymWordArch)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymWordN8 -> b) where
  wrap f = Fun $ \case
    Word8 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymWordN16 -> b) where
  wrap f = Fun $ \case
    Word16 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymWordN32 -> b) where
  wrap f = Fun $ \case
    Word32 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

instance (MonadSymbolic m, Wrap m n b) => Wrap m n (RuntimeValue SymWordN64 -> b) where
  wrap f = Fun $ \case
    Word64 arg -> pure $ wrap @m @n (f arg)
    _ -> throwError IllTyped

-- | Get the dynamically typed, symbolic value for a literal.
evalLiteral
  :: forall m n
   . MonadError SymbolicError m
  => KnownPos n
  => Literal
  -> m (Value m n)
evalLiteral = \case
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
      num' :: Num a => RuntimeValue a
      num' = pure $ fromInteger num

  LitFloat num -> do
    let num' = pure $ fromRational num
    pure $ Float num'

  LitDouble num -> do
    let num' = pure $ fromRational num
    pure $ Double num'

  _ -> throwError UnsupportedExpr
