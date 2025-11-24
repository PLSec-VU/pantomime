{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Symbolise
  ( symbolise
  , symboliseBind
  , symboliseBindMany
  ) where

import GHC.Plugins qualified as GHC
import GHC.Core.FamInstEnv (FamInstEnvs)
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
import GHC.TypeNats (KnownNat, natVal)

import Pantomime.Expr
import Pantomime.Subst
import Pantomime.Util (foldlBy)
import Pantomime.Grisette.SizedBV (sizedBVResize)
import Pantomime.Primitive.Reify
import Pantomime.Grisette.BitVector (IntN)
import Pantomime.Result

import Grisette.Unified (EvalModeTag (..))
import Grisette
  ( LogicalOp (..)
  , SignConversion (..)
  , SymOrd (..)
  , SymShift (..)
  , SymBool
  , SymEq (..)
  , SymFromIntegral (..)
  , GenSymSimple
  , SimpleMergeable (..)
  , mrgIf
  , genSymSimple
  )

import Control.Arrow (Arrow (..))
import Control.Monad (foldM, unless)

import Data.Bits (Bits (..), (.^.))
import Data.Typeable (Proxy (..), type (:~:) (..), eqT)

symbolise
  :: HasCallStack
  => () !> es
  => FamInstEnvs
  -> Subst es
  -> GHC.CoreExpr
  -> EvalExpr es
-- TODO: I'm now threading in the family instance environment for the primitive
-- reify functions. There's two annoying things here:
-- 1. I'm not using the inst environment in any of those calls actually
-- 2. Even if it would be required, we still only use it there. Threading
--    through seems not so clean...
--
-- For 1, I'll have to look at Reify of BitVector to see if I cannot get rid of
-- it in some smart way.
--
-- For 2, I could add the PrimOps to the substitution map instead of this
-- lookup. I feel like this one has merits in it's own right. Maybe we should do
-- this anyway, even if we end up fixing issue 1.
symbolise fam = go
  where
    -- TODO: I think we should add notes where we add helper functions like this
    -- to signify it is to ensure the callstack doesn't grow.
    go subst = \case
      GHC.Var var
        | Just expr <- lookupIdSubst subst var -> expr

        | Just expr <- GHC.maybeUnfoldingTemplate $ GHC.realIdUnfolding var
        -- TODO: I have this check for now, as it makes debugging a bit easier.
        -- Still, I don't think we want to keep this on the long haul. I guess
        -- a user could always write an axiom that says "use the original impl",
        -- so this isn't that bad. Maybe we should keep it? It is a lot nicer
        -- for users IMO! If we do, we should have an error that tells the user
        -- specifically the two options!
        , not . GHC.isOpaquePragma $ GHC.idInlinePragma var -> do
          -- TODO: As unfoldings are closed, should we be using the subst0 that
          -- was given at the initial call of this function? It would ensure
          -- the substitution grows a lot less in size. I'm not sure if this
          -- actually matters though.
          go subst expr

        | Just op <- GHC.isPrimOpId_maybe var -> do
          -- FIXME: Give proper platform size.
          symbolisePrimOp @64 fam op

        | Just dc <- GHC.isDataConId_maybe var -> do
          -- FIXME: This should get the proper platform size.
          let dc' = mkDataCon @64 dc
          pure $ mkLit dc'

        -- TODO: This case is to capture erased evidence variable. As far I as
        -- understand, these are constraints that could be completely eliminated.
        -- I don't understand how we are supposed to differentate from normal
        -- unit-typed variables. We should look into this...
        | eqType GHC.unitTy $ GHC.varType var -> do
          -- FIXME: This should get the proper platform size.
          let dc = mkDataCon @64 GHC.unitDataCon
          pure $ mkLit dc

        -- TODO: Give this a proper error.
        | otherwise -> do
          dbgE
            [ GHC.ppr $ GHC.varType var
            , GHC.ppr var
            , GHC.ppr $ GHC.idDetails var
            ]
          throwE ()

      GHC.Lit lit -> liftR $ mkLit <$> symboliseLit lit

      GHC.App fun arg -> do
        fun' <- go subst fun
        let arg' = go subst arg
        mkApp fun' arg'

      expr@(GHC.Lam bndr body) -> do
        let ty = substTy subst $ GHC.exprType expr
        pure $ mkLam ty \arg -> do
          subst' <- liftR $ extendSubst subst bndr arg
          go subst' body

      GHC.Let bind body -> do
        subst' <- liftR $ symboliseBind fam subst bind
        go subst' body

      GHC.Case scrut bndr _ty alts -> do
        -- Gather the spine and arguments of the scrutinee.
        scrut' <- go subst scrut
        (spine, args) <- collectScrut scrut'

        -- Altough perhaps overly cautious, we check whether the types line up.
        -- This is one of the places where values are forced, and thus one of
        -- the few places where we can perform a sanity check without messing
        -- with the evaluation semantic.
        let expectedTy = substTy subst $ GHC.varType bndr
        scrutTy <- liftR $ exprType scrut'
        unless (eqType scrutTy expectedTy) do
          throwE ()

        -- Extend the substitution with the case binder.
        subst' <- liftR $ extendSubst subst bndr (pure scrut')

        -- Create if-statement for every alternative.
        foldlBy mkUB alts \acc (GHC.Alt con bndrs rhs) -> do
          -- Gather the equality constraint for this branch.
          eq <- case spine of
            -- A coercion spine is only allowed to match default.
            Left _co
              | GHC.DEFAULT <- con -> pure true
              | otherwise -> throwE ()

            -- A literal spine should match the pattern.
            Right spine' -> liftR $ case con of
              -- FIXME: Create proper data con size.
              GHC.DataAlt dc -> eqLit spine' $ mkDataCon @64 dc
              GHC.LitAlt lit -> symboliseLit lit >>= eqLit spine'
              GHC.DEFAULT -> pure true

          -- TODO: Perhaps it's a good idea to check that the number of
          -- arguments match the binders (unless it is a DEFAULT, in which case
          -- any number of arguments is fine).

          -- Extend the substitution with the binders and evaluate the
          -- right-hand side.
          let branch = do
                subst'' <- liftR $ extendSubstMany subst' (zip bndrs args)
                go subst'' rhs

          -- We want to lazily evaluate branches. As such, we keep them unforced
          -- inside of the monad.
          mrgIf eq branch acc

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
  :: forall es fs
   . HasCallStack
  => () !> es
  => () !> fs
  => FamInstEnvs
  -> Subst fs
  -> GHC.CoreBind
  -> Result es (Subst fs)
symboliseBind fam subst = \case
  GHC.NonRec bndr rhs -> do
    let rhs' = symbolise fam subst rhs
    extendIdSubst subst bndr rhs'

  GHC.Rec pairs -> do
    let subst' :: forall gs. () !> gs => Result gs (Subst fs)
        subst' = extendIdSubstMany subst pairs'
        pairs' = second symbolise' <$> pairs
        symbolise' rhs = liftR subst' >>= \s -> symbolise fam s rhs
    subst'

symboliseBindMany
  :: forall f es fs
   . HasCallStack
  => () !> es
  => () !> fs
  => Foldable f
  => FamInstEnvs
  -> Subst fs
  -> f GHC.CoreBind
  -> Result es (Subst fs)
symboliseBindMany = foldM . symboliseBind

symboliseLit
  :: () !> es
  => GHC.Literal
  -> Result es Literal
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

  _ -> throw ()

symbolisePrimOp
  :: forall n es
   . HasCallStack
  => () !> es
  => KnownNat n
  => FamInstEnvs
  -> PrimOp
  -> EvalExpr es
symbolisePrimOp fam = \case
  -- Char operations:
  -------------------
  -- ChrOp -> throwE ()
  -- OrdOp -> throwE ()
  -- CharGtOp -> throwE ()
  -- CharGeOp -> throwE ()
  -- CharEqOp -> throwE ()
  -- CharNeOp -> throwE ()
  -- CharLtOp -> throwE ()
  -- CharLeOp -> throwE ()

  -- Int8 operations:
  -------------------
  Int8ToIntOp -> convert @(RHIntN 8) @(RHIntPW n) sizedBVResize
  Int8ToWord8Op -> convert @(RHIntN 8) @(RHWordN 8) toUnsigned
  Int8NegOp -> unary @(RHIntN 8) negate
  Int8AddOp -> binary @(RHIntN 8) (+)
  Int8SubOp -> binary @(RHIntN 8) (-)
  Int8MulOp -> binary @(RHIntN 8) (*)
  -- Int8QuotOp -> throwE ()
  -- Int8RemOp -> throwE ()
  -- Int8QuotRemOp -> throwE ()
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
  -- Int16QuotOp -> throwE ()
  -- Int16RemOp -> throwE ()
  -- Int16QuotRemOp -> throwE ()
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
  -- Int32QuotOp -> throwE ()
  -- Int32RemOp -> throwE ()
  -- Int32QuotRemOp -> throwE ()
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
  -- Int64QuotOp -> throwE ()
  -- Int64RemOp -> throwE ()
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
  -- IntToFloatOp -> throwE ()
  -- IntToDoubleOp -> throwE ()
  IntAddOp -> binary @(RHIntPW n) (+)
  IntSubOp -> binary @(RHIntPW n) (-)
  IntMulOp -> binary @(RHIntPW n) (*)
  -- IntAddCOp -> throwE ()
  -- IntSubCOp -> throwE ()
  -- IntMul2Op -> throwE ()
  -- IntMulMayOfloOp -> throwE ()
  -- IntQuotOp -> throwE ()
  -- IntRemOp -> throwE ()
  -- IntQuotRemOp -> throwE ()
  IntAndOp -> binary @(RHIntPW n) (.&.)
  IntOrOp -> binary @(RHIntPW n) (.|.)
  IntXorOp -> binary @(RHIntPW n) (.^.)
  IntNotOp -> unary @(RHIntPW n) complement
  IntNegOp -> unary @(RHIntPW n) negate
  -- IntSllOp -> binary $ shiftL' @(IntPW S ws)
  -- IntSraOp -> binary $ shiftRA' @(IntPW S ws)
  -- IntSrlOp -> binary $ shiftRL' @(IntPW S ws)
  IntEqOp -> cmp @(RHIntPW n) (.==)
  IntGeOp -> cmp @(RHIntPW n) (.>=)
  IntGtOp -> cmp @(RHIntPW n) (.>)
  IntLeOp -> cmp @(RHIntPW n) (.<=)
  IntLtOp -> cmp @(RHIntPW n) (.<)
  IntNeOp -> cmp @(RHIntPW n) (./=)

  -- Word8 operations:
  --------------------
  Word8ToWordOp -> convert @(RHWordN 8) @(RHWordPW n) sizedBVResize
  Word8ToInt8Op -> convert @(RHWordN 8) @(RHIntN 8) toSigned
  Word8AddOp -> binary @(RHWordN 8) (+)
  Word8SubOp -> binary @(RHWordN 8) (-)
  Word8MulOp -> binary @(RHWordN 8) (*)
  -- Word8QuotOp -> throwE ()
  -- Word8RemOp -> throwE ()
  -- Word8QuotRemOp -> throwE ()
  Word8AndOp -> binary @(RHWordN 8) (.&.)
  Word8OrOp -> binary @(RHWordN 8) (.|.)
  Word8XorOp -> binary @(RHWordN 8) (.^.)
  Word8NotOp -> unary @(RHWordN 8) complement
  Word8SllOp -> shft @(RHWordN 8) symShift
  Word8SrlOp -> shft @(RHWordN 8) symShiftNegated
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
  -- Word16QuotOp -> throwE ()
  -- Word16RemOp -> throwE ()
  -- Word16QuotRemOp -> throwE ()
  Word16AndOp -> binary @(RHWordN 16) (.&.)
  Word16OrOp -> binary @(RHWordN 16) (.|.)
  Word16XorOp -> binary @(RHWordN 16) (.^.)
  Word16NotOp -> unary @(RHWordN 16) complement
  Word16SllOp -> shft @(RHWordN 16) symShift
  Word16SrlOp -> shft @(RHWordN 16) symShiftNegated
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
  -- Word32QuotOp -> throwE ()
  -- Word32RemOp -> throwE ()
  -- Word32QuotRemOp -> throwE ()
  Word32AndOp -> binary @(RHWordN 32) (.&.)
  Word32OrOp -> binary @(RHWordN 32) (.|.)
  Word32XorOp -> binary @(RHWordN 32) (.^.)
  Word32NotOp -> unary @(RHWordN 32) complement
  Word32SllOp -> shft @(RHWordN 32) symShift
  Word32SrlOp -> shft @(RHWordN 32) symShiftNegated
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
  -- Word64QuotOp -> throwE ()
  -- Word64RemOp -> throwE ()
  Word64AndOp -> binary @(RHWordN 64) (.&.)
  Word64OrOp -> binary @(RHWordN 64) (.|.)
  Word64XorOp -> binary @(RHWordN 64) (.^.)
  Word64NotOp -> unary @(RHWordN 64) complement
  Word64SllOp -> shft @(RHWordN 64) symShift
  Word64SrlOp -> shft @(RHWordN 64) symShiftNegated
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
  -- WordToFloatOp -> throwE ()
  -- WordToDoubleOp -> throwE ()
  WordAddOp -> binary @(RHWordPW n) (+)
  WordSubOp -> binary @(RHWordPW n) (-)
  WordMulOp -> binary @(RHWordPW n) (*)
  -- WordAddCOp -> throwE ()
  -- WordSubCOp -> throwE ()
  -- WordAdd2Op -> throwE ()
  -- WordMul2Op -> throwE ()
  -- WordQuotOp -> throwE ()
  -- WordRemOp -> throwE ()
  -- WordQuotRemOp -> throwE ()
  -- WordQuotRem2Op -> throwE ()
  WordAndOp -> binary @(RHWordPW n) (.&.)
  WordOrOp -> binary @(RHWordPW n) (.|.)
  WordXorOp -> binary @(RHWordPW n) (.^.)
  WordNotOp -> unary @(RHWordPW n) complement
  WordSllOp -> shft @(RHWordPW n) symShift
  WordSrlOp -> shft @(RHWordPW n) symShiftNegated
  WordEqOp -> cmp @(RHWordPW n) (.==)
  WordGeOp -> cmp @(RHWordPW n) (.>=)
  WordGtOp -> cmp @(RHWordPW n) (.>)
  WordLeOp -> cmp @(RHWordPW n) (.<=)
  WordLtOp -> cmp @(RHWordPW n) (.<)
  WordNeOp -> cmp @(RHWordPW n) (./=)

  -- Tag operations:
  ------------------
  TagToEnumOp -> tagToEnum
  DataToTagSmallOp -> dataToTag
  DataToTagLargeOp -> dataToTag

  -- Error handling:
  ------------------
  RaiseOp -> raiseOp
  -- RaiseDivZeroOp -> undefined
  -- RaiseUnderflowOp -> undefined
  -- RaiseOverflowOp -> undefined
  -- RaiseIOOp -> undefined

  _ -> throwE ()
  where
    convert
      :: forall a b
       . ReifyBuiltin a
      => ReifyBuiltin b
      => (InterpRep es a -> InterpRep es b)
      -> EvalExpr es
    convert = builtinReify @(a ~> b) fam . liftF1'

    binary
      :: forall a
       . ReifyBuiltin a
      => (InterpRep es a -> InterpRep es a -> InterpRep es a)
      -> EvalExpr es
    binary = builtinReify @(a ~> a ~> a) fam . liftF2'

    unary
      :: forall a
       . ReifyBuiltin a
      => (InterpRep es a -> InterpRep es a)
      -> EvalExpr es
    unary = builtinReify @(a ~> a) fam . liftF1'

    cmp
      :: forall a
       . ReifyBuiltin a
      => (InterpRep es a -> InterpRep es a -> SymBool)
      -> EvalExpr es
    cmp f = builtinReify @(a ~> a ~> RHIntPW n) fam $ liftF2' \l r -> do
      mrgIte (f l r) 1 0

    -- TODO: I need to think of a good way to do arithmetic/logical shift as
    -- Grisette doesn't expose it readily... Perhaps the best is just a
    -- typeclass? I guess that could also remove the need for most of the stuff
    -- here even?
    shft
      :: forall a bv m
       . ReifyBuiltin a
      => KnownNat m
      => InterpRep es a ~ bv m
      => SymFromIntegral (IntN S n) (bv m)
      => SimpleMergeable (bv m)
      => GenSymSimple () (bv m)
      => (bv m -> bv m -> bv m)
      -> EvalExpr es
    shft f = builtinReify @(a ~> RHIntPW n ~> a) fam $ liftF2' \val idx -> do
      -- The bit-size of platform words.
      let size = fromIntegral $ natVal (Proxy @m)

      -- The bounds within which a shift is defined.
      let inBounds = 0 .<= idx .&& idx .< size

      -- We model undefined behaviour via an uninterpreted function.
      -- TODO: Perhaps there is a better way to name this such that we ensure we
      -- do not get name clashes? Ideally we use the unique of every shift
      -- operation we interpret to instantiate this function!
      -- FIXME: This doesn't take the arguments into account when shifting, so
      -- is actually a bit too permissive.
      let ub = genSymSimple () "UB.shift"

      -- The normal, within bounds computation
      let result = f val $ symFromIntegral idx

      -- The final result is defined only within the bounds.
      mrgIte inBounds result ub

    tagToEnum = builtinReify @(TagToEnumType n) fam $ liftF2 \ty arg -> do
      tag <- arg
      mkEnumCon tag ty

    raiseOp = builtinReify @RaiseType fam $ liftF5 \_l _r _a _b x -> do
      mkRaise x

    dataToTag = builtinReify @(DataToTagType n) fam $ liftF3 \_lev ty arg -> do
      -- Force the argument.
      arg' <- arg

      -- Ensure the argument is of the correct type.
      argTy <- liftR $ exprType arg'
      unless (eqType ty argTy) do
        throwE ()

      -- TODO: I dislike having this function here, maybe it should be a
      -- function inside of Expr? Especially since there is some detail here
      -- like how we convert datacon to tags.
      -- Get the DataCon tag.
      case fst $ collectArgs arg' of
        Lit (DataCon dc) -> pure (fromIntegral . GHC.dataConTagZ $ dc)
        Lit (EnumCon @m tag _tc) | Just Refl <- eqT @n @m -> pure tag
        _ -> throwE ()

-- | Alias for the 'tagToEnum#' reified type.
--
-- forall a. Int# -> a
type TagToEnumType n
  =  RTyVar_ 0
  +> RHIntPW n
  ~> RTyVar_ 0

-- | Alias for the 'dataToTag#' reified type.
--
-- forall (l :: Levity) (a :: TYPE (Boxed l)). l -> Int#
type DataToTagType n
  =  RTyVar 0 RLevity
  +> RTyVar 1 (RBoxedRep (RTyVar 0 RLevity))
  +> RTyVar 1 (RBoxedRep (RTyVar 0 RLevity))
  ~> RHIntPW n

-- :: forall
--    {l :: Levity}
--    {r :: RuntimeRep}
--    (a :: TYPE ('BoxedRep l))
--    (b :: TYPE r)
--  . a
-- -> b
type RaiseType
  =  RTyVar 0 RLevity
  +> RTyVar 1 RRuntimeRep
  +> RTyVar 2 (RBoxedRep (RTyVar 0 RLevity))
  +> RTyVar 3 (RTYPE (RTyVar 1 RRuntimeRep))
  +> RTyVar 2 (RBoxedRep (RTyVar 0 RLevity))
  ~> RTyVar 3 (RTYPE (RTyVar 1 RRuntimeRep))
