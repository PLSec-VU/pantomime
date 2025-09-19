{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Symbolise
  ( symbolise
  , symboliseBind
  , symboliseBindMany
  ) where

import GHC.Plugins qualified as GHC
import GHC.Builtin.PrimOps (PrimOp (..))
import GHC.Builtin.Types.Prim
  ( intPrimTy
  , int8PrimTy
  , int16PrimTy
  , int32PrimTy
  , int64PrimTy
  , wordPrimTy
  , word8PrimTy
  , word16PrimTy
  , word32PrimTy
  , word64PrimTy
  , byteArrayPrimTy
  )

import GHC.Stack (HasCallStack)
import GHC.TypeNats (KnownNat)

import Pantomime.Expr
import Pantomime.Subst
import Pantomime.Util (foldM')
import Pantomime.Grisette.SizedBV (sizedBVResize)
import Pantomime.Primitive.Reify

import Grisette
  ( LogicalOp (..)
  , SignConversion (..)
  , SymOrd (..)
  , SimpleMergeable (..)
  , SymBool
  , SymEq (..)
  , mrgIf
  )

import Control.Monad.Except (MonadError(..))
import Control.Monad (join, foldM, unless)
import Control.Arrow (Arrow(..))

import Data.Bits (Bits(..), (.^.))
import Data.Typeable (type (:~:)(..), eqT)

symbolise
  :: HasCallStack
  => Subst
  -> GHC.CoreExpr
  -> Eval Expr
symbolise = go
  where
    go subst = \case
      -- TODO: Maybe just pattern match on Var once and use multiple guards.
      GHC.Var var | Just expr <- lookupIdSubst subst var -> expr

      -- TODO: As unfoldings are closed, should we be using the subst0 that
      -- was given at the initial call of this function? It would ensure the
      -- substitution grows a lot less in size. I'm not sure if this actually
      -- matters though.
      GHC.Var var | GHC.CoreUnfolding { uf_tmpl } <- GHC.idUnfolding var -> do
        go subst uf_tmpl

      GHC.Var var | GHC.DFunUnfolding { .. } <- GHC.idUnfolding var -> do
        let dataCon = GHC.Var $ GHC.dataConWorkId df_con
        let inner = GHC.mkApps dataCon df_args
        let quantified = GHC.mkLams df_bndrs inner
        go subst quantified

      -- FIXME: Give proper platform size.
      GHC.Var var | Just op <- GHC.isPrimOpId_maybe var -> do
        symbolisePrimOp @64 op

      GHC.Var var | Just dc <- GHC.isDataConId_maybe var -> do
        -- FIXME: This should get the proper platform size.
        let dc' = mkDataCon @64 dc
        pure $ mkLit dc'

      -- TODO: Give this a proper error.
      GHC.Var _var -> throwError' ()

      GHC.Lit lit -> mkLit <$> symboliseLit lit

      GHC.App fun arg -> do
        fun' <- go subst fun
        let arg' = go subst arg
        mkApp fun' arg'

      expr@(GHC.Lam bndr body) -> do
        let ty = substTy subst $ GHC.exprType expr
        pure $ mkLam ty \arg -> do
          subst' <- extendSubst subst bndr arg
          go subst' body

      GHC.Let bind body -> do
        subst' <- symboliseBind subst bind
        go subst' body

      GHC.Case scrut bndr _ty alts -> do
        scrut' <- go subst scrut
        subst' <- extendSubst subst bndr $ pure scrut'

        (spine, args) <- collectScrut scrut'

        join $ foldM' mkUB alts \acc (GHC.Alt con bndrs rhs) -> do
          -- Check equality between alt pattern and the spine.
          eq <- case con of
            -- FIXME: Create proper data con size.
            GHC.DataAlt dc -> eqLit spine $ mkDataCon @64 dc
            GHC.LitAlt lit -> symboliseLit lit >>= eqLit spine
            GHC.DEFAULT -> pure true

          -- TODO: Perhaps it's a good idea to check that the number of
          -- arguments match the binders (unless it is a DEFAULT, in which case
          -- any number of arguments is fine).

          -- Extend the substitution with the binders and evaluate the
          -- right-hand side.
          let branch = extendSubstMany subst' (zip bndrs args) >>= flip go rhs

          -- We do not want to merge errors of values that are unreachable. As
          -- such, we first branch before joining the monad.
          pure $ mrgIf eq branch acc

      GHC.Cast body co -> do
        body' <- go subst body
        let co' = substCo subst co
        mkCast body' co'

      GHC.Tick _ body -> go subst body

      GHC.Type ty -> do
        let ty' = substTy subst ty
        pure $ mkType ty'

      GHC.Coercion co -> do
        let co' = substCo subst co
        pure $ mkCoercion co'

-- TODO: This is mutually recursive with 'symbolise'. I have to find a way not
-- to bloat the callstack!
symboliseBind
  :: HasCallStack
  => Subst
  -> GHC.CoreBind
  -> Eval Subst
symboliseBind subst = \case
  GHC.NonRec bndr rhs -> do
    let rhs' = symbolise subst rhs
    extendSubst subst bndr rhs'

  GHC.Rec pairs -> do
    let subst' = extendSubstMany subst pairs'
        pairs' = second symbolise' <$> pairs
        symbolise' rhs = subst' >>= flip symbolise rhs
    subst'

symboliseBindMany
  :: HasCallStack
  => Foldable f
  => Subst
  -> f GHC.CoreBind
  -> Eval Subst
symboliseBindMany = foldM symboliseBind

symboliseLit
  :: MonadError (EvalError ()) m
  => GHC.Literal
  -> m Literal
symboliseLit = \case
  GHC.LitNumber ty num -> do
    let num' :: Num s => s
        num' = fromInteger num
    case ty of
      -- FIXME: Give proper platform size.
      GHC.LitNumInt -> pure $ Int @64 num' intPrimTy
      GHC.LitNumInt8 -> pure $ Int @8 num' int8PrimTy
      GHC.LitNumInt16 -> pure $ Int @16 num' int16PrimTy
      GHC.LitNumInt32 -> pure $ Int @32 num' int32PrimTy
      GHC.LitNumInt64 -> pure $ Int @64 num' int64PrimTy
      -- FIXME: Give proper platform size.
      GHC.LitNumWord -> pure $ Word @64 num' wordPrimTy
      GHC.LitNumWord8 -> pure $ Word @8 num' word8PrimTy
      GHC.LitNumWord16 -> pure $ Word @16 num' word16PrimTy
      GHC.LitNumWord32 -> pure $ Word @32 num' word32PrimTy
      GHC.LitNumWord64 -> pure $ Word @64 num' word64PrimTy
      -- TODO: The BigNat primitive is a literal for BigNat# (which is a
      -- ByteArray#). Once we have byte array literals, we could encode this
      -- as such. For now, it is fine to just encode it as an Integer literal
      -- with type ByteArray#. As we constant fold literally everything anyway,
      -- it shouldn't be slow if we convert such a ByteArray# constant to a
      -- symbolic integer later.
      GHC.LitNumBigNat -> pure $ Integer num' byteArrayPrimTy

  -- GHC.LitFloat num -> do
  --   let num' = pure $ fromRational num
  --   pure $ Float num'

  -- GHC.LitDouble num -> do
  --   let num' = pure $ fromRational num
  --   pure $ Double num'

  _ -> throwError' ()

symbolisePrimOp
  :: forall n
   . HasCallStack
  => KnownNat n
  => PrimOp
  -> Eval Expr
symbolisePrimOp = \case
  -- Char operations:
  -------------------
  -- ChrOp -> throwError' ()
  -- OrdOp -> throwError' ()
  -- CharGtOp -> throwError' ()
  -- CharGeOp -> throwError' ()
  -- CharEqOp -> throwError' ()
  -- CharNeOp -> throwError' ()
  -- CharLtOp -> throwError' ()
  -- CharLeOp -> throwError' ()

  -- Int8 operations:
  -------------------
  Int8ToIntOp -> convert @(RHIntN 8) @(RHIntPW n) sizedBVResize
  Int8ToWord8Op -> convert @(RHIntN 8) @(RHWordN 8) toUnsigned
  Int8NegOp -> unary @(RHIntN 8) negate
  Int8AddOp -> binary @(RHIntN 8) (+)
  Int8SubOp -> binary @(RHIntN 8) (-)
  Int8MulOp -> binary @(RHIntN 8) (*)
  -- Int8QuotOp -> throwError' ()
  -- Int8RemOp -> throwError' ()
  -- Int8QuotRemOp -> throwError' ()
  -- Int8SllOp -> binary @(PIntN 8) shiftL'
  -- Int8SraOp -> binary @(PIntN 8) shiftRA'
  -- Int8SrlOp -> binary @(PIntN 8) shiftRL'
  Int8EqOp -> cmp @(RHIntN 8) (.==)
  Int8GeOp -> cmp @(RHIntN 8) (.>=)
  Int8GtOp -> cmp @(RHIntN 8) (.>)
  Int8LeOp -> cmp @(RHIntN 8) (.<=)
  Int8LtOp -> cmp @(RHIntN 8) (.<)
  Int8NeOp -> cmp @(RHIntN 8) (./=)

  -- Int16 operations:
  --------------------
  Int16ToIntOp -> convert @(RHIntN 16) @(RHIntPW n) sizedBVResize
  Int16ToWord16Op -> convert @(RHIntN 16) @(RHWordN 16) toUnsigned
  Int16NegOp -> unary @(RHIntN 16) negate
  Int16AddOp -> binary @(RHIntN 16) (+)
  Int16SubOp -> binary @(RHIntN 16) (-)
  Int16MulOp -> binary @(RHIntN 16) (*)
  -- Int16QuotOp -> throwError' ()
  -- Int16RemOp -> throwError' ()
  -- Int16QuotRemOp -> throwError' ()
  -- Int16SllOp -> binary @(PIntN 16) shiftL'
  -- Int16SraOp -> binary @(PIntN 16) shiftRA'
  -- Int16SrlOp -> binary @(PIntN 16) shiftRL'
  Int16EqOp -> cmp @(RHIntN 16) (.==)
  Int16GeOp -> cmp @(RHIntN 16) (.>=)
  Int16GtOp -> cmp @(RHIntN 16) (.>)
  Int16LeOp -> cmp @(RHIntN 16) (.<=)
  Int16LtOp -> cmp @(RHIntN 16) (.<)
  Int16NeOp -> cmp @(RHIntN 16) (./=)

  -- Int32 operations:
  --------------------
  Int32ToIntOp -> convert @(RHIntN 32) @(RHIntPW n) sizedBVResize
  Int32ToWord32Op -> convert @(RHIntN 32) @(RHWordN 32) toUnsigned
  Int32NegOp -> unary @(RHIntN 32) negate
  Int32AddOp -> binary @(RHIntN 32) (+)
  Int32SubOp -> binary @(RHIntN 32) (-)
  Int32MulOp -> binary @(RHIntN 32) (*)
  -- Int32QuotOp -> throwError' ()
  -- Int32RemOp -> throwError' ()
  -- Int32QuotRemOp -> throwError' ()
  -- Int32SllOp -> binary @(PIntN 32) shiftL'
  -- Int32SraOp -> binary @(PIntN 32) shiftRA'
  -- Int32SrlOp -> binary @(PIntN 32) shiftRL'
  Int32EqOp -> cmp @(RHIntN 32) (.==)
  Int32GeOp -> cmp @(RHIntN 32) (.>=)
  Int32GtOp -> cmp @(RHIntN 32) (.>)
  Int32LeOp -> cmp @(RHIntN 32) (.<=)
  Int32LtOp -> cmp @(RHIntN 32) (.<)
  Int32NeOp -> cmp @(RHIntN 32) (./=)

  -- Int64 operations:
  --------------------
  Int64ToIntOp -> convert @(RHIntN 64) @(RHIntPW n) sizedBVResize
  Int64ToWord64Op -> convert @(RHIntN 64) @(RHWordN 64) toUnsigned
  Int64NegOp -> unary @(RHIntN 64) negate
  Int64AddOp -> binary @(RHIntN 64) (+)
  Int64SubOp -> binary @(RHIntN 64) (-)
  Int64MulOp -> binary @(RHIntN 64) (*)
  -- Int64QuotOp -> throwError' ()
  -- Int64RemOp -> throwError' ()
  -- Int64SllOp -> binary @(PIntN 64) shiftL'
  -- Int64SraOp -> binary @(PIntN 64) shiftRA'
  -- Int64SrlOp -> binary @(PIntN 64) shiftRL'
  Int64EqOp -> cmp @(RHIntN 64) (.==)
  Int64GeOp -> cmp @(RHIntN 64) (.>=)
  Int64GtOp -> cmp @(RHIntN 64) (.>)
  Int64LeOp -> cmp @(RHIntN 64) (.<=)
  Int64LtOp -> cmp @(RHIntN 64) (.<)
  Int64NeOp -> cmp @(RHIntN 64) (./=)

  -- Int operations:
  ------------------
  IntToInt8Op -> convert @(RHIntPW n) @(RHIntN 8) sizedBVResize
  IntToInt16Op -> convert @(RHIntPW n) @(RHIntN 16) sizedBVResize
  IntToInt32Op -> convert @(RHIntPW n) @(RHIntN 32) sizedBVResize
  IntToInt64Op -> convert @(RHIntPW n) @(RHIntN 64) sizedBVResize
  IntToWordOp -> convert @(RHIntPW n) @(RHWordPW n) toUnsigned
  -- IntToFloatOp -> throwError' ()
  -- IntToDoubleOp -> throwError' ()
  IntAddOp -> binary @(RHIntPW n) (+)
  IntSubOp -> binary @(RHIntPW n) (-)
  IntMulOp -> binary @(RHIntPW n) (*)
  -- IntAddCOp -> throwError' ()
  -- IntSubCOp -> throwError' ()
  -- IntMul2Op -> throwError' ()
  -- IntMulMayOfloOp -> throwError' ()
  -- IntQuotOp -> throwError' ()
  -- IntRemOp -> throwError' ()
  -- IntQuotRemOp -> throwError' ()
  IntAndOp -> binary @(RHIntPW n) (.&.)
  IntOrOp -> binary @(RHIntPW n) (.|.)
  IntXorOp -> binary @(RHIntPW n) (.^.)
  IntNotOp -> unary @(RHIntPW n) complement
  IntNegOp -> unary @(RHIntPW n) negate
  -- IntSllOp -> binary $ shiftL' @(IntPW S ws)
  -- IntSraOp -> binary $ shiftRA' @(IntPW S ws)
  -- IntSrlOp -> binary $ shiftRL' @(IntPW S ws)
  IntGtOp -> cmp @(RHIntPW n) (.==)
  IntGeOp -> cmp @(RHIntPW n) (.>=)
  IntEqOp -> cmp @(RHIntPW n) (.>)
  IntNeOp -> cmp @(RHIntPW n) (.<=)
  IntLtOp -> cmp @(RHIntPW n) (.<)
  IntLeOp -> cmp @(RHIntPW n) (./=)

  -- Word8 operations:
  --------------------
  Word8ToWordOp -> convert @(RHWordN 8) @(RHWordPW n) sizedBVResize
  Word8ToInt8Op -> convert @(RHWordN 8) @(RHIntN 8) toSigned
  Word8AddOp -> binary @(RHWordN 8) (+)
  Word8SubOp -> binary @(RHWordN 8) (-)
  Word8MulOp -> binary @(RHWordN 8) (*)
  -- Word8QuotOp -> throwError' ()
  -- Word8RemOp -> throwError' ()
  -- Word8QuotRemOp -> throwError' ()
  Word8AndOp -> binary @(RHWordN 8) (.&.)
  Word8OrOp -> binary @(RHWordN 8) (.|.)
  Word8XorOp -> binary @(RHWordN 8) (.^.)
  Word8NotOp -> unary @(RHWordN 8) complement
  -- Word8SllOp -> binary $ shiftL' @(WordN S 8)
  -- Word8SrlOp -> binary $ shiftRL' @(WordN S 8)
  Word8EqOp -> cmp @(RHWordN 8) (.==)
  Word8GeOp -> cmp @(RHWordN 8) (.>=)
  Word8GtOp -> cmp @(RHWordN 8) (.>)
  Word8LeOp -> cmp @(RHWordN 8) (.<=)
  Word8LtOp -> cmp @(RHWordN 8) (.<)
  Word8NeOp -> cmp @(RHWordN 8) (./=)

  -- Word16 operations:
  ---------------------
  Word16ToWordOp -> convert @(RHWordN 16) @(RHWordPW n) sizedBVResize
  Word16ToInt16Op -> convert @(RHWordN 16) @(RHIntN 16) toSigned
  Word16AddOp -> binary @(RHWordN 16) (+)
  Word16SubOp -> binary @(RHWordN 16) (-)
  Word16MulOp -> binary @(RHWordN 16) (*)
  -- Word16QuotOp -> throwError' ()
  -- Word16RemOp -> throwError' ()
  -- Word16QuotRemOp -> throwError' ()
  Word16AndOp -> binary @(RHWordN 16) (.&.)
  Word16OrOp -> binary @(RHWordN 16) (.|.)
  Word16XorOp -> binary @(RHWordN 16) (.^.)
  Word16NotOp -> unary @(RHWordN 16) complement
  -- Word16SllOp -> binary $ shiftL' @(WordN S 16)
  -- Word16SrlOp -> binary $ shiftRL' @(WordN S 16)
  Word16EqOp -> cmp @(RHWordN 16) (.==)
  Word16GeOp -> cmp @(RHWordN 16) (.>=)
  Word16GtOp -> cmp @(RHWordN 16) (.>)
  Word16LeOp -> cmp @(RHWordN 16) (.<=)
  Word16LtOp -> cmp @(RHWordN 16) (.<)
  Word16NeOp -> cmp @(RHWordN 16) (./=)

  -- Word32 operations:
  ---------------------
  Word32ToWordOp -> convert @(RHWordN 32) @(RHWordPW n) sizedBVResize
  Word32ToInt32Op -> convert @(RHWordN 32) @(RHIntN 32) toSigned
  Word32AddOp -> binary @(RHWordN 32) (+)
  Word32SubOp -> binary @(RHWordN 32) (-)
  Word32MulOp -> binary @(RHWordN 32) (*)
  -- Word32QuotOp -> throwError' ()
  -- Word32RemOp -> throwError' ()
  -- Word32QuotRemOp -> throwError' ()
  Word32AndOp -> binary @(RHWordN 32) (.&.)
  Word32OrOp -> binary @(RHWordN 32) (.|.)
  Word32XorOp -> binary @(RHWordN 32) (.^.)
  Word32NotOp -> unary @(RHWordN 32) complement
  -- Word32SllOp -> binary $ shiftL' @(WordN S 32)
  -- Word32SrlOp -> binary $ shiftRL' @(WordN S 32)
  Word32EqOp -> cmp @(RHWordN 32) (.==)
  Word32GeOp -> cmp @(RHWordN 32) (.>=)
  Word32GtOp -> cmp @(RHWordN 32) (.>)
  Word32LeOp -> cmp @(RHWordN 32) (.<=)
  Word32LtOp -> cmp @(RHWordN 32) (.<)
  Word32NeOp -> cmp @(RHWordN 32) (./=)

  -- Word64 operations:
  ---------------------
  Word64ToWordOp -> convert @(RHWordN 64) @(RHWordPW n) sizedBVResize
  Word64ToInt64Op -> convert @(RHWordN 64) @(RHIntN 64) toSigned
  Word64AddOp -> binary @(RHWordN 64) (+)
  Word64SubOp -> binary @(RHWordN 64) (-)
  Word64MulOp -> binary @(RHWordN 64) (*)
  -- Word64QuotOp -> throwError' ()
  -- Word64RemOp -> throwError' ()
  Word64AndOp -> binary @(RHWordN 64) (.&.)
  Word64OrOp -> binary @(RHWordN 64) (.|.)
  Word64XorOp -> binary @(RHWordN 64) (.^.)
  Word64NotOp -> unary @(RHWordN 64) complement
  -- Word64SllOp -> binary $ shiftL' @(WordN S 64)
  -- Word64SrlOp -> binary $ shiftRL' @(WordN S 64)
  Word64EqOp -> cmp @(RHWordN 64) (.==)
  Word64GeOp -> cmp @(RHWordN 64) (.>=)
  Word64GtOp -> cmp @(RHWordN 64) (.>)
  Word64LeOp -> cmp @(RHWordN 64) (.<=)
  Word64LtOp -> cmp @(RHWordN 64) (.<)
  Word64NeOp -> cmp @(RHWordN 64) (./=)

  -- Word operations:
  -------------------
  WordToWord8Op -> convert @(RHWordPW n) @(RHWordN 8) sizedBVResize
  WordToWord16Op -> convert @(RHWordPW n) @(RHWordN 16) sizedBVResize
  WordToWord32Op -> convert @(RHWordPW n) @(RHWordN 32) sizedBVResize
  WordToWord64Op -> convert @(RHWordPW n) @(RHWordN 64) sizedBVResize
  WordToIntOp -> convert @(RHWordPW n) @(RHIntPW n) toSigned
  -- WordToFloatOp -> throwError' ()
  -- WordToDoubleOp -> throwError' ()
  WordAddOp -> binary @(RHWordPW n) (+)
  WordSubOp -> binary @(RHWordPW n) (-)
  WordMulOp -> binary @(RHWordPW n) (*)
  -- WordAddCOp -> throwError' ()
  -- WordSubCOp -> throwError' ()
  -- WordAdd2Op -> throwError' ()
  -- WordMul2Op -> throwError' ()
  -- WordQuotOp -> throwError' ()
  -- WordRemOp -> throwError' ()
  -- WordQuotRemOp -> throwError' ()
  -- WordQuotRem2Op -> throwError' ()
  WordAndOp -> binary @(RHWordPW n) (.&.)
  WordOrOp -> binary @(RHWordPW n) (.|.)
  WordXorOp -> binary @(RHWordPW n) (.^.)
  WordNotOp -> unary @(RHWordPW n) complement
  -- WordSllOp -> binary $ shiftL' @(WordPW S ws)
  -- WordSrlOp -> binary $ shiftRL' @(WordPW S ws)
  WordGtOp -> cmp @(RHWordPW n) (.==)
  WordGeOp -> cmp @(RHWordPW n) (.>=)
  WordEqOp -> cmp @(RHWordPW n) (.>)
  WordNeOp -> cmp @(RHWordPW n) (.<=)
  WordLtOp -> cmp @(RHWordPW n) (.<)
  WordLeOp -> cmp @(RHWordPW n) (./=)

  -- Tag operations:
  ------------------
  TagToEnumOp -> tagToEnum
  DataToTagSmallOp -> dataToTag
  DataToTagLargeOp -> dataToTag

  _ -> throwError' ()
  where
    convert
      :: forall a b
       . ReifyBuiltin a
      => ReifyBuiltin b
      => (InterpRep a -> InterpRep b)
      -> Eval Expr
    convert = builtinReify @(a ~> b) . liftF1'

    binary
      :: forall a
       . ReifyBuiltin a
      => (InterpRep a -> InterpRep a -> InterpRep a)
      -> Eval Expr
    binary = builtinReify @(a ~> a ~> a) . liftF2'

    unary
      :: forall a
       . ReifyBuiltin a
      => (InterpRep a -> InterpRep a)
      -> Eval Expr
    unary = builtinReify @(a ~> a) . liftF1'

    cmp
      :: forall a
       . ReifyBuiltin a
      => (InterpRep a -> InterpRep a -> SymBool)
      -> Eval Expr
    cmp f = builtinReify @(a ~> a ~> RHIntPW n) $ liftF2' \l r -> do
      mrgIte (f l r) 1 0

    tagToEnum = builtinReify @(AlphaType +> RHIntPW n ~> RPoly AlphaType) do
      liftF2 \ty arg -> do
        tag <- arg
        mkEnumCon tag ty

    dataToTag = builtinReify 
      @(BetaLevity +> AlphaBoxed BetaLevity +> RPoly AlphaType ~> RHIntPW n) do
        liftF3 \_lev ty arg -> do
          arg' <- arg

          -- Ensure the argument is of the correct type.
          argTy <- exprType arg'
          unless (eqType ty argTy) do
            throwError' ()

          -- Get the DataCon tag if possible.
          case fst $ collectArgs arg' of
            Lit (DataCon @m tag _tc) | Just Refl <- eqT @n @m -> pure tag
            _ -> throwError' ()
