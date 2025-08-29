{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Symbolise
  ( symbolise
  , symboliseBind
  , symboliseBindMany
  ) where

import GHC.Stack (HasCallStack)
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
  )

import Pantomime.Expr
import Pantomime.Util (foldM')

import Grisette (mrgIf, LogicalOp (..), SignConversion (..), SymOrd (..), SimpleMergeable (..), SymBool, SymEq (..))

import Control.Monad.Except (MonadError(..))
import Control.Monad (join, foldM)
import Control.Arrow (Arrow(..))
import Pantomime.Grisette.BitVector (IntN, WordN)
import Grisette.Unified (EvalModeTag(..))
import Data.Typeable (type (:~:)(..), eqT, Proxy (..))
import GHC.TypeNats (Nat, KnownNat)
import GHC.TypeLits (natVal)
import Data.Type.Bool (type (||))
import Data.Type.Equality (type (==))
import Pantomime.Grisette.SizedBV (sizedBVResize)
import Data.Bits (Bits(..), (.^.))

symbolise
  :: HasCallStack
  => Subst
  -> GHC.CoreExpr
  -> Eval Expr
symbolise = go
  where
    go subst = \case
      -- TODO: Tidy up unfolding code!
      GHC.Var var | GHC.CoreUnfolding { uf_tmpl } <- GHC.idUnfolding var -> do
        go subst uf_tmpl

      GHC.Var var | GHC.DFunUnfolding { df_bndrs, df_con, df_args } <- GHC.idUnfolding var -> do
        let dataCon = GHC.Var $ GHC.dataConWorkId df_con
        let inner = GHC.mkApps dataCon df_args
        let quantified = GHC.mkLams df_bndrs inner
        go subst quantified

      -- FIXME: Give proper word size.
      GHC.Var var | Just op <- GHC.isPrimOpId_maybe var -> symbolisePrimOp @64 op

      GHC.Var var | Just _ <- GHC.isPrimOpId_maybe var -> throwError' ()

      GHC.Var var | Just dc <- GHC.isDataConId_maybe var -> do
        -- FIXME: This should get the proper platform size.
        let dc' = mkDataCon @64 dc
        pure $ mkLit dc'

      GHC.Var var -> lookupId subst var

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
  :: Foldable f
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
      -- TODO: The BigNat primitive operations are kind of "hidden". Somehow, we
      -- want to wrap the behaviour!
      -- LitNumBigNat -> throwError ()
      _ -> throwError' ()

  -- GHC.LitFloat num -> do
  --   let num' = pure $ fromRational num
  --   pure $ Float num'

  -- GHC.LitDouble num -> do
  --   let num' = pure $ fromRational num
  --   pure $ Double num'

  _ -> throwError' ()

symbolisePrimOp
  :: forall n
   . KnownNat n
  => PrimOp
  -> Eval Expr
symbolisePrimOp = \case
  -- OrdOp -> throwError' ()

  -- Char operations:
  -------------------
  -- ChrOp -> throwError' ()
  -- CharGtOp -> throwError' ()
  -- CharGeOp -> throwError' ()
  -- CharEqOp -> throwError' ()
  -- CharNeOp -> throwError' ()
  -- CharLtOp -> throwError' ()
  -- CharLeOp -> throwError' ()

  -- Int8 operations:
  -------------------
  Int8ToIntOp -> prim @(PIntN 8 ~> PIntPW n) sizedBVResize
  Int8ToWord8Op -> prim @(PIntN 8 ~> PWordN 8) toUnsigned
  Int8NegOp -> unary @(PIntN 8) negate
  Int8AddOp -> binary @(PIntN 8) (+)
  Int8SubOp -> binary @(PIntN 8) (-)
  Int8MulOp -> binary @(PIntN 8) (*)
  -- Int8QuotOp -> throwError' ()
  -- Int8RemOp -> throwError' ()
  -- Int8QuotRemOp -> throwError' ()
  -- Int8SllOp -> binary @(PIntN 8) shiftL'
  -- Int8SraOp -> binary @(PIntN 8) shiftRA'
  -- Int8SrlOp -> binary @(PIntN 8) shiftRL'
  Int8EqOp -> cmp @(PIntN 8) (.==)
  Int8GeOp -> cmp @(PIntN 8) (.>=)
  Int8GtOp -> cmp @(PIntN 8) (.>)
  Int8LeOp -> cmp @(PIntN 8) (.<=)
  Int8LtOp -> cmp @(PIntN 8) (.<)
  Int8NeOp -> cmp @(PIntN 8) (./=)

  -- Int16 operations:
  --------------------
  Int16ToIntOp -> prim @(PIntN 16 ~> PIntPW n) sizedBVResize
  Int16ToWord16Op -> prim @(PIntN 16 ~> PWordN 16) toUnsigned
  Int16NegOp -> unary @(PIntN 16) negate
  Int16AddOp -> binary @(PIntN 16) (+)
  Int16SubOp -> binary @(PIntN 16) (-)
  Int16MulOp -> binary @(PIntN 16) (*)
  -- Int16QuotOp -> throwError' ()
  -- Int16RemOp -> throwError' ()
  -- Int16QuotRemOp -> throwError' ()
  -- Int16SllOp -> binary @(PIntN 16) shiftL'
  -- Int16SraOp -> binary @(PIntN 16) shiftRA'
  -- Int16SrlOp -> binary @(PIntN 16) shiftRL'
  Int16EqOp -> cmp @(PIntN 16) (.==)
  Int16GeOp -> cmp @(PIntN 16) (.>=)
  Int16GtOp -> cmp @(PIntN 16) (.>)
  Int16LeOp -> cmp @(PIntN 16) (.<=)
  Int16LtOp -> cmp @(PIntN 16) (.<)
  Int16NeOp -> cmp @(PIntN 16) (./=) 

  -- Int32 operations:
  --------------------
  Int32ToIntOp -> prim @(PIntN 32 ~> PIntPW n) sizedBVResize
  Int32ToWord32Op -> prim @(PIntN 32 ~> PWordN 32) toUnsigned
  Int32NegOp -> unary @(PIntN 32) negate
  Int32AddOp -> binary @(PIntN 32) (+)
  Int32SubOp -> binary @(PIntN 32) (-)
  Int32MulOp -> binary @(PIntN 32) (*)
  -- Int32QuotOp -> throwError' ()
  -- Int32RemOp -> throwError' ()
  -- Int32QuotRemOp -> throwError' ()
  -- Int32SllOp -> binary @(PIntN 32) shiftL'
  -- Int32SraOp -> binary @(PIntN 32) shiftRA'
  -- Int32SrlOp -> binary @(PIntN 32) shiftRL'
  Int32EqOp -> cmp @(PIntN 32) (.==)
  Int32GeOp -> cmp @(PIntN 32) (.>=)
  Int32GtOp -> cmp @(PIntN 32) (.>)
  Int32LeOp -> cmp @(PIntN 32) (.<=)
  Int32LtOp -> cmp @(PIntN 32) (.<)
  Int32NeOp -> cmp @(PIntN 32) (./=) 

  -- Int64 operations:
  --------------------
  Int64ToIntOp -> prim @(PIntN 64 ~> PIntPW n) sizedBVResize
  Int64ToWord64Op -> prim @(PIntN 64 ~> PWordN 64) toUnsigned
  Int64NegOp -> unary @(PIntN 64) negate
  Int64AddOp -> binary @(PIntN 64) (+)
  Int64SubOp -> binary @(PIntN 64) (-)
  Int64MulOp -> binary @(PIntN 64) (*)
  -- Int64QuotOp -> throwError' ()
  -- Int64RemOp -> throwError' ()
  -- Int64SllOp -> binary @(PIntN 64) shiftL'
  -- Int64SraOp -> binary @(PIntN 64) shiftRA'
  -- Int64SrlOp -> binary @(PIntN 64) shiftRL'
  Int64EqOp -> cmp @(PIntN 64) (.==)
  Int64GeOp -> cmp @(PIntN 64) (.>=)
  Int64GtOp -> cmp @(PIntN 64) (.>)
  Int64LeOp -> cmp @(PIntN 64) (.<=)
  Int64LtOp -> cmp @(PIntN 64) (.<)
  Int64NeOp -> cmp @(PIntN 64) (./=) 

  -- Int operations:
  ------------------
  IntToInt8Op -> prim @(PIntPW n ~> PIntN 8) sizedBVResize
  IntToInt16Op -> prim @(PIntPW n ~> PIntN 16) sizedBVResize
  IntToInt32Op -> prim @(PIntPW n ~> PIntN 32) sizedBVResize
  IntToInt64Op -> prim @(PIntPW n ~> PIntN 64) sizedBVResize
  IntToWordOp -> prim @(PIntPW n ~> PWordPW n) toUnsigned
  -- IntToFloatOp -> throwError' ()
  -- IntToDoubleOp -> throwError' ()
  IntAddOp -> binary @(PIntPW n) (+)
  IntSubOp -> binary @(PIntPW n) (-)
  IntMulOp -> binary @(PIntPW n) (*)
  -- IntAddCOp -> throwError' ()
  -- IntSubCOp -> throwError' ()
  -- IntMul2Op -> throwError' ()
  -- IntMulMayOfloOp -> throwError' ()
  -- IntQuotOp -> throwError' ()
  -- IntRemOp -> throwError' ()
  -- IntQuotRemOp -> throwError' ()
  IntAndOp -> binary @(PIntPW n) (.&.)
  IntOrOp -> binary @(PIntPW n) (.|.)
  IntXorOp -> binary @(PIntPW n) (.^.)
  IntNotOp -> unary @(PIntPW n) complement
  IntNegOp -> unary @(PIntPW n) negate
  -- IntSllOp -> binary $ shiftL' @(IntPW S ws)
  -- IntSraOp -> binary $ shiftRA' @(IntPW S ws)
  -- IntSrlOp -> binary $ shiftRL' @(IntPW S ws)
  IntGtOp -> cmp @(PIntPW n) (.==)
  IntGeOp -> cmp @(PIntPW n) (.>=)
  IntEqOp -> cmp @(PIntPW n) (.>)
  IntNeOp -> cmp @(PIntPW n) (.<=)
  IntLtOp -> cmp @(PIntPW n) (.<)
  IntLeOp -> cmp @(PIntPW n) (./=)

  -- Word8 operations:
  --------------------
  Word8ToWordOp -> prim @(PWordN 8 ~> PWordPW n) sizedBVResize
  Word8ToInt8Op -> prim @(PWordN 8 ~> PIntN 8) toSigned
  Word8AddOp -> binary @(PWordN 8) (+)
  Word8SubOp -> binary @(PWordN 8) (-)
  Word8MulOp -> binary @(PWordN 8) (*)
  -- Word8QuotOp -> throwError' ()
  -- Word8RemOp -> throwError' ()
  -- Word8QuotRemOp -> throwError' ()
  Word8AndOp -> binary @(PWordN 8) (.&.)
  Word8OrOp -> binary @(PWordN 8) (.|.)
  Word8XorOp -> binary @(PWordN 8) (.^.)
  Word8NotOp -> unary @(PWordN 8) complement
  -- Word8SllOp -> binary $ shiftL' @(WordN S 8)
  -- Word8SrlOp -> binary $ shiftRL' @(WordN S 8)
  Word8EqOp -> cmp @(PWordN 8) (.==)
  Word8GeOp -> cmp @(PWordN 8) (.>=)
  Word8GtOp -> cmp @(PWordN 8) (.>)
  Word8LeOp -> cmp @(PWordN 8) (.<=)
  Word8LtOp -> cmp @(PWordN 8) (.<)
  Word8NeOp -> cmp @(PWordN 8) (./=)

  -- Word16 operations:
  ---------------------
  Word16ToWordOp -> prim @(PWordN 16 ~> PWordPW n) sizedBVResize
  Word16ToInt16Op -> prim @(PWordN 16 ~> PIntN 16) toSigned
  Word16AddOp -> binary @(PWordN 16) (+)
  Word16SubOp -> binary @(PWordN 16) (-)
  Word16MulOp -> binary @(PWordN 16) (*)
  -- Word16QuotOp -> throwError' ()
  -- Word16RemOp -> throwError' ()
  -- Word16QuotRemOp -> throwError' ()
  Word16AndOp -> binary @(PWordN 16) (.&.)
  Word16OrOp -> binary @(PWordN 16) (.|.)
  Word16XorOp -> binary @(PWordN 16) (.^.)
  Word16NotOp -> unary @(PWordN 16) complement
  -- Word16SllOp -> binary $ shiftL' @(WordN S 16)
  -- Word16SrlOp -> binary $ shiftRL' @(WordN S 16)
  Word16EqOp -> cmp @(PWordN 16) (.==)
  Word16GeOp -> cmp @(PWordN 16) (.>=)
  Word16GtOp -> cmp @(PWordN 16) (.>)
  Word16LeOp -> cmp @(PWordN 16) (.<=)
  Word16LtOp -> cmp @(PWordN 16) (.<)
  Word16NeOp -> cmp @(PWordN 16) (./=)

  -- Word32 operations:
  ---------------------
  Word32ToWordOp -> prim @(PWordN 32 ~> PWordPW n) sizedBVResize
  Word32ToInt32Op -> prim @(PWordN 32 ~> PIntN 32) toSigned
  Word32AddOp -> binary @(PWordN 32) (+)
  Word32SubOp -> binary @(PWordN 32) (-)
  Word32MulOp -> binary @(PWordN 32) (*)
  -- Word32QuotOp -> throwError' ()
  -- Word32RemOp -> throwError' ()
  -- Word32QuotRemOp -> throwError' ()
  Word32AndOp -> binary @(PWordN 32) (.&.)
  Word32OrOp -> binary @(PWordN 32) (.|.)
  Word32XorOp -> binary @(PWordN 32) (.^.)
  Word32NotOp -> unary @(PWordN 32) complement
  -- Word32SllOp -> binary $ shiftL' @(WordN S 32)
  -- Word32SrlOp -> binary $ shiftRL' @(WordN S 32)
  Word32EqOp -> cmp @(PWordN 32) (.==)
  Word32GeOp -> cmp @(PWordN 32) (.>=)
  Word32GtOp -> cmp @(PWordN 32) (.>)
  Word32LeOp -> cmp @(PWordN 32) (.<=)
  Word32LtOp -> cmp @(PWordN 32) (.<)
  Word32NeOp -> cmp @(PWordN 32) (./=)

  -- Word64 operations:
  ---------------------
  Word64ToWordOp -> prim @(PWordN 64 ~> PWordPW n) sizedBVResize
  Word64ToInt64Op -> prim @(PWordN 64 ~> PIntN 64) toSigned
  Word64AddOp -> binary @(PWordN 64) (+)
  Word64SubOp -> binary @(PWordN 64) (-)
  Word64MulOp -> binary @(PWordN 64) (*)
  -- Word64QuotOp -> throwError' ()
  -- Word64RemOp -> throwError' ()
  Word64AndOp -> binary @(PWordN 64) (.&.)
  Word64OrOp -> binary @(PWordN 64) (.|.)
  Word64XorOp -> binary @(PWordN 64) (.^.)
  Word64NotOp -> unary @(PWordN 64) complement
  -- Word64SllOp -> binary $ shiftL' @(WordN S 64)
  -- Word64SrlOp -> binary $ shiftRL' @(WordN S 64)
  Word64EqOp -> cmp @(PWordN 64) (.==)
  Word64GeOp -> cmp @(PWordN 64) (.>=)
  Word64GtOp -> cmp @(PWordN 64) (.>)
  Word64LeOp -> cmp @(PWordN 64) (.<=)
  Word64LtOp -> cmp @(PWordN 64) (.<)
  Word64NeOp -> cmp @(PWordN 64) (./=)

  -- Word operations:
  -------------------
  WordToWord8Op -> prim @(PWordPW n ~> PWordN 8) sizedBVResize
  WordToWord16Op -> prim @(PWordPW n ~> PWordN 16) sizedBVResize
  WordToWord32Op -> prim @(PWordPW n ~> PWordN 32) sizedBVResize
  WordToWord64Op -> prim @(PWordPW n ~> PWordN 64) sizedBVResize
  WordToIntOp -> prim @(PWordPW n ~> PIntPW n) toSigned
  -- WordToFloatOp -> throwError' ()
  -- WordToDoubleOp -> throwError' ()
  WordAddOp -> binary @(PWordPW n) (+)
  WordSubOp -> binary @(PWordPW n) (-)
  WordMulOp -> binary @(PWordPW n) (*)
  -- WordAddCOp -> throwError' ()
  -- WordSubCOp -> throwError' ()
  -- WordAdd2Op -> throwError' ()
  -- WordMul2Op -> throwError' ()
  -- WordQuotOp -> throwError' ()
  -- WordRemOp -> throwError' ()
  -- WordQuotRemOp -> throwError' ()
  -- WordQuotRem2Op -> throwError' ()
  WordAndOp -> binary @(PWordPW n) (.&.)
  WordOrOp -> binary @(PWordPW n) (.|.)
  WordXorOp -> binary @(PWordPW n) (.^.)
  WordNotOp -> unary @(PWordPW n) complement
  -- WordSllOp -> binary $ shiftL' @(WordPW S ws)
  -- WordSrlOp -> binary $ shiftRL' @(WordPW S ws)
  WordGtOp -> cmp @(PWordPW n) (.==)
  WordGeOp -> cmp @(PWordPW n) (.>=)
  WordEqOp -> cmp @(PWordPW n) (.>)
  WordNeOp -> cmp @(PWordPW n) (.<=)
  WordLtOp -> cmp @(PWordPW n) (.<)
  WordLeOp -> cmp @(PWordPW n) (./=)

  -- Tag operations:
  -- TagToEnumOp -> undefined
  -- DataToTagSmallOp -> undefined
  -- DataToTagLargeOp -> undefined

  _ -> throwError' ()
  where
    prim
      :: forall a
       . Primitive a
      => PrimRep a
      -> Eval Expr
    prim = pure . primitive @a

    binary
      :: forall a
       . Primitive a
      => (PrimRep a -> PrimRep a -> PrimRep a)
      -> Eval Expr
    binary f = pure $ primitive @(a ~> a ~> a) f

    unary
      :: forall a
       . Primitive a
      => (PrimRep a -> PrimRep a)
      -> Eval Expr
    unary f = pure $ primitive @(a ~> a) f

    cmp
      :: forall a
       . Primitive a
      => (PrimRep a -> PrimRep a -> SymBool)
      -> Eval Expr
    cmp f = prim @(a ~> a ~> PIntPW n) \l r -> mrgIte (f l r) 1 0

-- | Primitive type.
--
-- Primitives have a Haskell type and may be converted to and from expressions.
class Primitive a where
  type PrimRep a

  primTy :: GHC.Type
  primArg :: Expr -> Maybe (PrimRep a)
  primitive :: PrimRep a -> Expr

-- | Function primitive.
data (~>) a b
infixr ~>

instance (Primitive a, Primitive b) => Primitive (a ~> b) where
  type PrimRep (a ~> b) = PrimRep a -> PrimRep b

  primTy = GHC.mkFunTy GHC.FTF_T_T GHC.ManyTy (primTy @a) (primTy @b)

  -- TODO: This is kind of misuse, as we really just cannot implement this for
  -- functions. It should be a superclass I feel.
  primArg = const Nothing

  primitive f = do
    let ty = primTy @(a ~> b)
    mkLam ty \arg -> do
      prim <- arg >>= whyFail' () . primArg @a
      let result = f prim
      pure $ primitive @b result

-- | Fixed size integer primitive.
data PIntN (n :: Nat)

instance
  ( KnownNat n
  , (n == 8 || n == 16 || n == 32 || n == 64) ~ True
  ) => Primitive (PIntN n) where
  type PrimRep (PIntN n) = IntN S n

  primTy = case natVal @n Proxy of
    8 -> int8PrimTy
    16 -> int16PrimTy
    32 -> int32PrimTy
    64 -> int64PrimTy
    _ -> error "unreachable due to typeclass constraint"

  primArg = \case
    Lit (Int @m tag ty)
      | Just Refl <- eqT @n @m
      , ty == primTy @(PIntN n) -> pure tag
    _ -> Nothing

  primitive x = do
    let ty = primTy @(PIntN n)
    mkLit $ mkIntN x ty

-- | Platform sized integer primitive.
data PIntPW (n :: Nat)

instance KnownNat n => Primitive (PIntPW n) where
  type PrimRep (PIntPW n) = IntN S n

  primTy = intPrimTy

  primArg = \case
    Lit (Int @m tag ty)
      | Just Refl <- eqT @n @m
      , ty == primTy @(PIntPW n) -> pure tag
    _ -> Nothing

  primitive x = do
    let ty = primTy @(PIntPW n)
    mkLit $ mkIntN x ty

-- | Fixed size natural primitive.
data PWordN (n :: Nat)

instance
  ( KnownNat n
  , (n == 8 || n == 16 || n == 32 || n == 64) ~ True
  ) => Primitive (PWordN n) where
  type PrimRep (PWordN n) = WordN S n

  primTy = case natVal @n Proxy of
    8 -> word8PrimTy
    16 -> word16PrimTy
    32 -> word32PrimTy
    64 -> word64PrimTy
    _ -> error "unreachable due to typeclass constraint"

  primArg = \case
    Lit (Word @m tag ty)
      | Just Refl <- eqT @n @m
      , ty == primTy @(PWordN n) -> pure tag
    _ -> Nothing

  primitive x = do
    let ty = primTy @(PWordN n)
    mkLit $ mkWordN x ty

-- | Platform word sized natural primitive.
data PWordPW (n :: Nat)

instance KnownNat n => Primitive (PWordPW n) where
  type PrimRep (PWordPW n) = WordN S n

  primTy = wordPrimTy

  primArg = \case
    Lit (Word @m tag ty)
      | Just Refl <- eqT @n @m
      , ty == primTy @(PWordPW n) -> pure tag
    _ -> Nothing

  primitive x = do
    let ty = primTy @(PWordPW n)
    mkLit $ mkWordN x ty
