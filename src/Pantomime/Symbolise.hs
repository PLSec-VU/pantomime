{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Symbolise
  ( symbolise
  , symboliseBind
  , symboliseBindMany
  ) where

import GHC.Builtin.Types.Prim
import GHC.Core.Predicate (isDictId)
import GHC.Utils.Misc (HasCallStack)
import GHC.Plugins qualified as GHC

import Pantomime.Expr4
import Pantomime.Util (foldM')

import Grisette (mrgIf, LogicalOp (..))

import Control.Monad.Except (MonadError(..))
import Control.Monad (join, foldM)
import Control.Arrow (Arrow(..))

import Debug.Trace (trace)

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

      -- TODO: Handle primitive operations.
      -- GHC.Var var | Just op <- GHC.isPrimOpId_maybe var -> translatePrimOp @n op
      GHC.Var var | Just _ <- GHC.isPrimOpId_maybe var -> throwError' ()

      GHC.Var var | Just dc <- GHC.isDataConId_maybe var -> do
        -- FIXME: This should get the proper platform size.
        let dc' = mkDataCon @64 dc
        pure $ mkLit dc'

      GHC.Var var -> lookupId subst var `catchError` \_ -> do
        dbg 
          [ GHC.ppr var
          , GHC.ppr $ isDictId var
          , GHC.ppr $ GHC.idUnfolding var
          ] 
        throwError' ()

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

        -- FIXME: Something goes wrong here...
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

dbg
  :: GHC.Outputable o
  => o
  -> Eval ()
dbg m = trace (GHC.showSDocUnsafe $ GHC.ppr m) $ pure ()
