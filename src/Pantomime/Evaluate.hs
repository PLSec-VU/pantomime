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

module Pantomime.Evaluate
  ( evaluate
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Builtin.PrimOps (PrimOp (..))
import GHC.Builtin.Types.Prim

import GHC.Data.Maybe (rightToMaybe, catMaybes)

import Control.Monad (forM)

import Data.Functor ((<&>))
import Data.Bits (Bits(..), (.^.))
import Data.Composition ((.:))

import Grisette hiding (Fresh, Rec, (<+>))
import Grisette.Unified (EvalModeTag (..))

import Pantomime.Util
import Pantomime.WordSize
import Pantomime.Runtime
import Pantomime.Value
import Pantomime.Environment
import Pantomime.MonadEval

import Effectful
import Effectful.Error.Static (Error, throwError_)
import Effectful.GHC.TH
import Effectful.GHC.TyThing
import Effectful.GHC.External
import Effectful.Grisette.Fresh

-- | Evaluate an expression into a symbolic Value.
evaluate
  :: forall es ws
   . Error EvalError :> es
  => Fresh :> es
  => HasFamInstEnvs :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => KnownWordSize ws
  => Environment es ws
  -> CoreExpr
  -> Eff es (Value (Eff es) ws)
evaluate env = \case
  Var var | Opaque _ <- inl_inline $ idInlinePragma var -> do
    -- dbg' "OPAQUE:"
    -- dbg $ varType var
    -- dbg var
    lookupIdEnv env var

  Var var | Just op <- isPrimOpId_maybe var -> evalPrimOp op
  Var var | Just dataCon <- isDataConId_maybe var -> evalDataCon dataCon

  Var var | CoreUnfolding { uf_tmpl } <- idUnfolding var -> do
    evaluate env uf_tmpl

  Var var | DFunUnfolding { df_bndrs, df_con, df_args } <- idUnfolding var -> do
    let dataCon = Var $ dataConWorkId df_con
    let inner = mkApps dataCon df_args
    let quantified = mkLams df_bndrs inner
    evaluate env quantified

  Var var | Just expr <- lookupLocalEnv env var -> evaluate env expr

  Var var -> lookupIdEnv env var

  Lit lit -> Primitive <$> evalLiteral lit

  Lam bndr body -> do
    let argTy = substTyEnv env $ varType bndr
    pure . Fun argTy $ \arg -> do
      env' <- extendEnv env bndr arg
      evaluate env' body

  App fun arg -> do
    fun' <- evaluate env fun
    arg' <- evaluate env arg
    applyValue fun' arg'

  Let (NonRec bndr arg) body -> do
    evaluate env $ Lam bndr body `App` arg

  -- Perhaps we could handle these by allowing a Tick annotation to specify an
  -- invariant. Otherwise though, we don't really care about recursive
  -- definitions. I guess bounded recursion would be nice to have, but let's
  -- leave this for now.
  Let (Rec _) _ -> throwError_ UnsupportedExpr

  Case scrut bndr ty alts -> do
    -- Evaluate the scrutinee and extend the environment using the case binder.
    scrut' <- evaluate env scrut
    env' <- extendEnv env bndr scrut'

    -- Gather the constraints to run each alternative and their body.
    alts' <- forM alts $ evalAlt env' scrut'

    -- TODO: Shouldn't this be a bottom value instead? I.e. if we don't have a
    -- irrefutable pattern match, we reach bottom.
    -- Get an Invalid as a default value.
    let ty' = substTyEnv env ty
    invalid <- invalidValue ty'

    -- Fold the alternatives into a large if-then-else.
    result <- foldM' invalid alts' \fl (cond, rhs) -> do
      evalIte cond rhs fl

    pure $ force @S (spine scrut') result

  Cast expr co -> do
    let co' = substCoEnv env co
    value <- evaluate env expr
    mkCast' co' value

  -- Ticks do not affect evaluation, thus we can skip it.
  Tick _ expr -> evaluate env expr

  Type ty -> do
    let ty' = substTyEnv env ty
    pure $ Ty ty'

  Coercion co -> do
    let co' = substCoEnv env co
    pure $ Co co'

-- | Return the condition to run this alternative and its symbolic rhs.
--
-- Expects the case binder to already be bound to the scrutinee in the
-- environment.
evalAlt
  :: forall es ws
   . Error EvalError :> es
  => Fresh :> es
  => HasFamInstEnvs :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => KnownWordSize ws
  => Environment es ws
  -> Value (Eff es) ws
  -> CoreAlt
  -> Eff es (SymBool, Value (Eff es) ws)
evalAlt env scrut = \case
  Alt (DataAlt dataCon) bndrs rhs -> do
    -- Ensure the scrutinee is actually an ADT.
    scrut' <- case scrut of
      Data adt -> pure adt
      _ -> throwError_ IllTyped

    -- Whether the tag of this ADT is equivalent to the DataCon.
    let conditional = onlyBool $ adtIsDataCon scrut' dataCon

    -- Extend the environment with the field for each binder.
    fields <- whyFail' IllTyped $ adtDataConFields scrut' dataCon
    env' <- extendManyEnv env $ zip bndrs fields

    -- Evaluate the right-hand side with the extended environment.
    rhs' <- evaluate env' rhs

    -- Return the condition to run this branch and the symbolic right-hand side.
    pure (conditional, rhs')

  Alt (LitAlt lit) [] rhs -> do
    -- The scrutinee has to be a primitive to match the literal alt.
    scrut' <- case scrut of
      Primitive prim -> pure prim
      _ -> throwError_ IllTyped

    -- Compare the literal, to the scrutinee.
    lit' <- evalLiteral lit
    conditional <- onlyPrimEq scrut' lit'

    -- Evaluate the rhs.
    rhs' <- evaluate env rhs

    -- Return the condition to take this branch and the branch itself.
    pure (conditional, rhs')

  Alt DEFAULT [] rhs -> do
    rhs' <- evaluate env rhs
    pure (true, rhs')

  _ -> throwError_ UnsupportedExpr

-- | Gathers only the boolean part of the constraint.
--
-- This will discard any of the constraints that lead to runtime errors. This is
-- to ensure we do not duplicate constraints. Instead, use Forceable instances
-- to actually force values.
onlyBool :: RuntimeValue S SymBool -> SymBool
onlyBool = symAnd
  . catMaybes
  . fmap rightToMaybe
  . overestimateUnionValues
  . unRuntimeS

onlyPrimEq
  :: forall es ws
   . Error EvalError :> es
  => KnownWordSize ws
  => Primitive S ws
  -> Primitive S ws
  -> Eff es SymBool
onlyPrimEq = curry $ \case
  (Int lhs, Int rhs) -> cmp lhs rhs
  (Int8 lhs, Int8 rhs) -> cmp lhs rhs
  (Int16 lhs, Int16 rhs) -> cmp lhs rhs
  (Int32 lhs, Int32 rhs) -> cmp lhs rhs
  (Int64 lhs, Int64 rhs) -> cmp lhs rhs
  (Word lhs, Word rhs) -> cmp lhs rhs
  (Word8 lhs, Word8 rhs) -> cmp lhs rhs
  (Word16 lhs, Word16 rhs) -> cmp lhs rhs
  (Word32 lhs, Word32 rhs) -> cmp lhs rhs
  (Word64 lhs, Word64 rhs) -> cmp lhs rhs
  (Float lhs, Float rhs) -> cmp lhs rhs
  (Double lhs, Double rhs) -> cmp lhs rhs
  _ -> throwError_ IllTyped
  where
    cmp
      :: Mergeable a
      => SymEq a
      => RuntimeValue S a
      -> RuntimeValue S a
      -> Eff es SymBool
    cmp = pure . onlyBool .: mrgLiftA2 (.==)

evalDataCon
  :: forall es ws
   . Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => Fresh :> es
  => HasFamInstEnvs :> es
  => KnownWordSize ws
  => DataCon
  -> Eff es (Value (Eff es) ws)
evalDataCon dataCon = do
  -- The root creates the actually symbolic DataCon using the given type
  -- instantiation.
  let root = evalDataConInst dataCon

  -- The number of type arguments we actually require.
  let kinds = ((),) . tyVarKind <$> dataConUnivTyVars dataCon

  -- Create an n-ary function accepting types, which will be used to instantiate
  -- the data constructor.
  final <- nArity root kinds $ \univ _ -> \case
    Ty ty -> pure $ univ <> [ty]
    _ -> throwError_ IllTyped

  -- We start with an emtpy list of type instances.
  final []

-- | Evaluate a DataCon with the given types as its instantiation.
--
-- This will create a function value with the number of arguments required by
-- the DataCon. The type of these arguments is dictated by the type arguments
-- passed to the function by use of 'dataConInstArgTys'. I.e. the given types
-- should be those applied to the TyCon when constructing the final type.
evalDataConInst
  :: forall es ws
   . Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => Fresh :> es
  => HasFamInstEnvs :> es
  => KnownWordSize ws
  => DataCon
  -- ^ The DataCon for which we will create a symbolic instance.
  -> [Type]
  -- ^ The types with which we will instantiate universal quantifiers of the
  -- DataCon.
  -> Eff es (Value (Eff es) ws)
evalDataConInst dataCon tyArgs = do
  -- Gather the types of the binders.
  let bndrTys = ((),) . scaledThing <$> dataConInstArgTys dataCon tyArgs

  -- The root is an ADT matching the given DataCon.
  let root fields = Data <$> adtFromDataCon dataCon tyArgs fields

  -- Accumulate a function that passes its arguments to the root.
  final <- nArity root bndrTys $ \fields _ arg -> do
    -- Constrain the field of the ADT to be equivalent to the argument.
    -- TODO: I think we should change the nArity function no? We can just do
    -- with only returning per element instead of accumulating like this. We
    -- are also ignoring the attached argument in all uses.
    pure $ fields <> [arg]

  final []

-- | Get the value corresponding to a literal.
evalLiteral
  :: forall es ws
   . Error EvalError :> es
  => KnownWordSize ws
  => Literal
  -> Eff es (Primitive S ws)
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
    _ -> throwError_ UnsupportedExpr
    where
      num' :: Num a => RuntimeValue S a
      num' = pure $ fromInteger num

  LitFloat num -> do
    let num' = pure $ fromRational num
    pure $ Float num'

  LitDouble num -> do
    let num' = pure $ fromRational num
    pure $ Double num'

  _ -> throwError_ UnsupportedExpr

-- | Get the value corresponding to a primitive operation.
-- TODO: I want to add support for rem and quot.
evalPrimOp
  :: forall es ws
   . Error EvalError :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => HasFamInstEnvs :> es
  => Fresh :> es
  => KnownWordSize ws
  => PrimOp
  -> Eff es (Value (Eff es) ws)
evalPrimOp = \case
  CharGtOp -> throwError_ UnsupportedExpr
  CharGeOp -> throwError_ UnsupportedExpr
  CharEqOp -> throwError_ UnsupportedExpr
  CharNeOp -> throwError_ UnsupportedExpr
  CharLtOp -> throwError_ UnsupportedExpr
  CharLeOp -> throwError_ UnsupportedExpr
  OrdOp -> throwError_ UnsupportedExpr
  Int8ToIntOp -> unary $ toIntArch @8
  IntToInt8Op -> unary $ toIntSized @8
  Int8NegOp -> unary $ negate @SymIntN8
  Int8AddOp -> binary $ (+) @SymIntN8
  Int8SubOp -> binary $ (-) @SymIntN8
  Int8MulOp -> binary $ (*) @SymIntN8
  Int8QuotOp -> throwError_ UnsupportedExpr
  Int8RemOp -> throwError_ UnsupportedExpr
  Int8QuotRemOp -> throwError_ UnsupportedExpr
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
  Word8QuotOp -> throwError_ UnsupportedExpr
  Word8RemOp -> throwError_ UnsupportedExpr
  Word8QuotRemOp -> throwError_ UnsupportedExpr
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
  Int16QuotOp -> throwError_ UnsupportedExpr
  Int16RemOp -> throwError_ UnsupportedExpr
  Int16QuotRemOp -> throwError_ UnsupportedExpr
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
  Word16QuotOp -> throwError_ UnsupportedExpr
  Word16RemOp -> throwError_ UnsupportedExpr
  Word16QuotRemOp -> throwError_ UnsupportedExpr
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
  Int32QuotOp -> throwError_ UnsupportedExpr
  Int32RemOp -> throwError_ UnsupportedExpr
  Int32QuotRemOp -> throwError_ UnsupportedExpr
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
  Word32QuotOp -> throwError_ UnsupportedExpr
  Word32RemOp -> throwError_ UnsupportedExpr
  Word32QuotRemOp -> throwError_ UnsupportedExpr
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
  Int64QuotOp -> throwError_ UnsupportedExpr
  Int64RemOp -> throwError_ UnsupportedExpr
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
  Word64QuotOp -> throwError_ UnsupportedExpr
  Word64RemOp -> throwError_ UnsupportedExpr
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
  IntMul2Op -> throwError_ UnsupportedExpr
  IntMulMayOfloOp -> throwError_ UnsupportedExpr
  IntQuotOp -> throwError_ UnsupportedExpr
  IntRemOp -> throwError_ UnsupportedExpr
  IntQuotRemOp -> throwError_ UnsupportedExpr
  IntAndOp -> binary $ (.&.) @(SymInt ws)
  IntOrOp -> binary $ (.|.) @(SymInt ws)
  IntXorOp -> binary $ (.^.) @(SymInt ws)
  IntNotOp -> unary $ complement @(SymInt ws)
  IntNegOp -> unary $ negate @(SymInt ws)
  IntAddCOp -> throwError_ UnsupportedExpr
  IntSubCOp -> throwError_ UnsupportedExpr
  IntGtOp -> binary $ symGt @(SymInt ws)
  IntGeOp -> binary $ symGe @(SymInt ws)
  IntEqOp -> binary $ symEq @(SymInt ws)
  IntNeOp -> binary $ symNe @(SymInt ws)
  IntLtOp -> binary $ symLt @(SymInt ws)
  IntLeOp -> binary $ symLe @(SymInt ws)
  ChrOp -> throwError_ UnsupportedExpr
  IntToWordOp -> unary $ toUnsigned @(SymWord ws) @(SymInt ws)
  IntToFloatOp -> throwError_ UnsupportedExpr
  IntToDoubleOp -> throwError_ UnsupportedExpr
  WordToFloatOp -> throwError_ UnsupportedExpr
  WordToDoubleOp -> throwError_ UnsupportedExpr
  IntSllOp -> binary $ symShiftL' @(SymInt ws)
  IntSraOp -> binary $ symShiftRA' @(SymInt ws)
  IntSrlOp -> binary $ symShiftRL' @(SymInt ws)
  WordAddOp -> binary $ (+) @(SymWord ws)
  WordAddCOp -> throwError_ UnsupportedExpr
  WordSubCOp -> throwError_ UnsupportedExpr
  WordAdd2Op -> throwError_ UnsupportedExpr
  WordSubOp -> binary $ (-) @(SymWord ws)
  WordMulOp -> binary $ (*) @(SymWord ws)
  WordMul2Op -> throwError_ UnsupportedExpr
  WordQuotOp -> throwError_ UnsupportedExpr
  WordRemOp -> throwError_ UnsupportedExpr
  WordQuotRemOp -> throwError_ UnsupportedExpr
  WordQuotRem2Op -> throwError_ UnsupportedExpr
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
  TagToEnumOp -> pure . Fun (tyVarKind alphaTyVar) $ \case
    Ty ty -> pure . Fun intPrimTy $ \case
      Primitive (Int tag) -> do
        -- TODO: Comment this!
        value <- freshValue @es @ws ty
        adt <- case value of
          Data adt -> pure $ adt { adtTag = tag }
          _ -> throwError_ IllTyped

        -- Return the new ADT with matching tag.
        pure $ Data adt
      _ -> throwError_ IllTyped
    _ -> throwError_ IllTyped
  DataToTagSmallOp -> pure dataToTag
  DataToTagLargeOp -> pure dataToTag
  _ -> throwError_ UnsupportedExpr
  where
    -- We don't distinguish between small or large tags, thus we have one
    -- implementation for dataToTag.
    --
    -- This function has the following Haskell type:
    --
    -- forall {l::levity} (a::TYPE (BoxedRep l)). a -> Int#
    dataToTag :: Value (Eff es) ws
    dataToTag = Fun levPolyAlphaTy $ \case
      Ty levity -> pure . Fun (mkTyConApp boxedRepDataConTyCon [levity]) $ \case
        Ty ty -> pure . Fun ty $ \case
          Data adt -> do
            let tag = Int $ adtTag adt
            pure $ Primitive tag
          _ -> throwError_ IllTyped
        _ -> throwError_ IllTyped
      _ -> throwError_ IllTyped

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
  :: Error EvalError :> es
  => Wrap ws (RuntimeValue S a -> RuntimeValue S b -> RuntimeValue S c)
  => (a -> b -> c)
  -> Eff es (Value (Eff es) ws)
binary = pure . wrap . liftA2 @(RuntimeValue S)

unary
  :: Error EvalError :> es
  => Wrap ws (RuntimeValue S a -> RuntimeValue S b)
  => (a -> b)
  -> Eff es (Value (Eff es) ws)
unary = pure . wrap . fmap @(RuntimeValue S)

class Wrap ws a where
  wrap :: Error EvalError :> es => a -> Value (Eff es) ws

instance Wrap ws (RuntimeValue S (SymInt ws)) where
  wrap = Primitive . Int . fmap unSymInt

instance Wrap ws (RuntimeValue S SymIntN8) where
  wrap = Primitive . Int8

instance Wrap ws (RuntimeValue S SymIntN16) where
  wrap = Primitive . Int16

instance Wrap ws (RuntimeValue S SymIntN32) where
  wrap = Primitive . Int32

instance Wrap ws (RuntimeValue S SymIntN64) where
  wrap = Primitive . Int64

instance KnownWordSize ws => Wrap ws (RuntimeValue S (SymWord ws)) where
  wrap = Primitive . Word . fmap unSymWord

instance Wrap ws (RuntimeValue S SymWordN8) where
  wrap = Primitive . Word8

instance Wrap ws (RuntimeValue S SymWordN16) where
  wrap = Primitive . Word16

instance Wrap ws (RuntimeValue S SymWordN32) where
  wrap = Primitive . Word32

instance Wrap ws (RuntimeValue S SymWordN64) where
  wrap = Primitive . Word64

instance Wrap ws b => Wrap ws (RuntimeValue S (SymInt ws) -> b) where
  wrap f = Fun intPrimTy $ \case
    Primitive (Int arg) -> pure $ wrap @ws (f $ arg <&> SymInt)
    _ -> throwError_ IllTyped

instance Wrap ws b => Wrap ws (RuntimeValue S SymIntN8 -> b) where
  wrap f = Fun int8PrimTy $ \case
    Primitive (Int8 arg) -> pure $ wrap @ws (f arg)
    _ -> throwError_ IllTyped

instance Wrap ws b => Wrap ws (RuntimeValue S SymIntN16 -> b) where
  wrap f = Fun int16PrimTy $ \case
    Primitive (Int16 arg) -> pure $ wrap @ws (f arg)
    _ -> throwError_ IllTyped

instance Wrap ws b => Wrap ws (RuntimeValue S SymIntN32 -> b) where
  wrap f = Fun int32PrimTy $ \case
    Primitive (Int32 arg) -> pure $ wrap @ws (f arg)
    _ -> throwError_ IllTyped

instance Wrap ws b => Wrap ws (RuntimeValue S SymIntN64 -> b) where
  wrap f = Fun int64PrimTy $ \case
    Primitive (Int64 arg) -> pure $ wrap @ws (f arg)
    _ -> throwError_ IllTyped

instance Wrap ws b => Wrap ws (RuntimeValue S (SymWord ws) -> b) where
  wrap f = Fun wordPrimTy $ \case
    Primitive (Word arg) -> pure $ wrap @ws (f $ arg <&> SymWord)
    _ -> throwError_ IllTyped

instance Wrap ws b => Wrap ws (RuntimeValue S SymWordN8 -> b) where
  wrap f = Fun word8PrimTy $ \case
    Primitive (Word8 arg) -> pure $ wrap @ws (f arg)
    _ -> throwError_ IllTyped

instance Wrap ws b => Wrap ws (RuntimeValue S SymWordN16 -> b) where
  wrap f = Fun word16PrimTy $ \case
    Primitive (Word16 arg) -> pure $ wrap @ws (f arg)
    _ -> throwError_ IllTyped

instance Wrap ws b => Wrap ws (RuntimeValue S SymWordN32 -> b) where
  wrap f = Fun word32PrimTy $ \case
    Primitive (Word32 arg) -> pure $ wrap @ws (f arg)
    _ -> throwError_ IllTyped

instance Wrap ws b => Wrap ws (RuntimeValue S SymWordN64 -> b) where
  wrap f = Fun word64PrimTy $ \case
    Primitive (Word64 arg) -> pure $ wrap @ws (f arg)
    _ -> throwError_ IllTyped
