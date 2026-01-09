{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Symbolise
  ( symbolise
  , symboliseBind
  , symboliseBindMany
  ) where

import GHC.Plugins qualified as GHC

import Pantomime.Literal (BuiltInTyCon)
import Pantomime.Expr
import Pantomime.Subst
import Pantomime.Util (foldlBy)

import Grisette (LogicalOp (..), mrgIf)

import Control.Arrow (Arrow (..))
import Control.Monad (foldM, unless)

import Effectful
import Effectful.Error.Static
import Effectful.GHC.External
import Effectful.Context

symbolise
  :: HasCallStack
  => Error () :> es
  => HasFamInstEnvs :> es
  => Context Reader BuiltInTyCon :> es
  => Subst es
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
--
-- NOTE: Since I extended Eval to allow this effect, it is not so bad. Still,
-- I think it would be good to implement 2. For 1, we would first need to allow
-- the typeclass instance to have different effects. This also has some
-- downsides, so it might not be worth the hassle.
symbolise = go
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

        | Just dc <- GHC.isDataConId_maybe var -> do
          -- FIXME: This should get the proper platform size.
          let dc' = mkDataCon @64 dc
          pure $ mkCon dc'

        -- TODO: This case is to capture erased evidence variable. As far I as
        -- understand, these are constraints that could be completely eliminated.
        -- I don't understand how we are supposed to differentate from normal
        -- unit-typed variables. We should look into this...
        | eqType GHC.unitTy $ GHC.varType var -> do
          -- FIXME: This should get the proper platform size.
          let dc = mkDataCon @64 GHC.unitDataCon
          pure $ mkCon dc

        -- TODO: Give this a proper error.
        | otherwise -> do
          dbgE
            [ GHC.ppr $ GHC.varType var
            , GHC.ppr var
            , GHC.ppr $ GHC.idDetails var
            ]
          throwE ()

      -- GHC.Lit lit -> liftEff $ mkLit <$> symboliseLit lit
      -- FIXME: I'm not sure how to handle literals here, as this always assumes
      -- something about their format.
      --
      -- Maybe it could be part of a user axiom? The annoying bit is that I
      -- would rather not have to require these axioms if you don't actually use
      -- the Haskell primitive types.
      GHC.Lit _lit -> undefined

      GHC.App fun arg -> do
        fun' <- go subst fun
        let arg' = go subst arg
        mkApp fun' arg'

      expr@(GHC.Lam bndr body) -> do
        let ty = substTy subst $ GHC.exprType expr
        pure $ mkLam ty \arg -> do
          subst' <- liftEff $ extendSubst subst bndr arg
          go subst' body

      GHC.Let bind body -> do
        subst' <- liftEff $ symboliseBind subst bind
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
        scrutTy <- liftEff $ exprType scrut'
        unless (eqType scrutTy expectedTy) do
          throwE ()

        -- Extend the substitution with the case binder.
        subst' <- liftEff $ extendSubst subst bndr (pure scrut')

        -- Create if-statement for every alternative.
        foldlBy mkUB alts \acc (GHC.Alt con bndrs rhs) -> do
          -- Gather the equality constraint for this branch.
          eq <- case spine of
            -- A coercion spine is only allowed to match default.
            Left _co
              | GHC.DEFAULT <- con -> pure true
              | otherwise -> throwE ()

            -- A literal spine should match the pattern.
            Right spine' -> liftEff $ case con of
              -- FIXME: Create proper data con size.
              GHC.DataAlt dc -> eqCon spine' $ mkDataCon @64 dc
              GHC.DEFAULT -> pure true
              -- NOTE: Due to the way primitives are implemented, we never
              -- scrutinise GHC literals directly.
              GHC.LitAlt _ -> throwError ()

          -- TODO: Perhaps it's a good idea to check that the number of
          -- arguments match the binders (unless it is a DEFAULT, in which case
          -- any number of arguments is fine).

          -- Extend the substitution with the binders and evaluate the
          -- right-hand side.
          let branch = do
                subst'' <- liftEff $ extendSubstMany subst' (zip bndrs args)
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
  => Error () :> es
  => Error () :> fs
  => HasFamInstEnvs :> fs
  => Context Reader BuiltInTyCon :> fs
  => Subst fs
  -> GHC.CoreBind
  -> Eff es (Subst fs)
symboliseBind subst = \case
  GHC.NonRec bndr rhs -> do
    let rhs' = symbolise subst rhs
    extendIdSubst subst bndr rhs'

  GHC.Rec pairs -> do
    let subst' :: forall gs. Error () :> gs => Eff gs (Subst fs)
        subst' = extendIdSubstMany subst pairs'
        pairs' = second symbolise' <$> pairs
        symbolise' rhs = liftEff subst' >>= \s -> symbolise s rhs
    subst'

symboliseBindMany
  :: forall f es fs
   . HasCallStack
  => Error () :> es
  => Error () :> fs
  => Foldable f
  => HasFamInstEnvs :> fs
  => Context Reader BuiltInTyCon :> fs
  => Subst fs
  -> f GHC.CoreBind
  -> Eff es (Subst fs)
symboliseBindMany = foldM symboliseBind

-- symboliseLit
--   :: Error () :> es
--   => GHC.Literal
--   -> Eff es Literal
-- symboliseLit = \case
--   GHC.LitNumber ty num -> do
--     let num' :: Num s => s
--         num' = fromInteger num
--     case ty of
--       -- FIXME: Give proper platform size.
--       GHC.LitNumInt -> pure $ Int @64 num' intPrimTy
--       GHC.LitNumInt8 -> pure $ Int @8 num' int8PrimTy
--       GHC.LitNumInt16 -> pure $ Int @16 num' int16PrimTy
--       GHC.LitNumInt32 -> pure $ Int @32 num' int32PrimTy
--       GHC.LitNumInt64 -> pure $ Int @64 num' int64PrimTy
--       -- FIXME: Give proper platform size.
--       GHC.LitNumWord -> pure $ Word @64 num' wordPrimTy
--       GHC.LitNumWord8 -> pure $ Word @8 num' word8PrimTy
--       GHC.LitNumWord16 -> pure $ Word @16 num' word16PrimTy
--       GHC.LitNumWord32 -> pure $ Word @32 num' word32PrimTy
--       GHC.LitNumWord64 -> pure $ Word @64 num' word64PrimTy
--       -- TODO: The BigNat primitive is a literal for BigNat# (which is a
--       -- ByteArray#). Once we have byte array literals, we could encode this
--       -- as such. For now, it is fine to just encode it as an Integer literal
--       -- with type ByteArray#. As we constant fold literally everything anyway,
--       -- it shouldn't be slow if we convert such a ByteArray# constant to a
--       -- symbolic integer later.
--       GHC.LitNumBigNat -> pure $ Integer num' byteArrayPrimTy

--   -- GHC.LitFloat num -> do
--   --   let num' = pure $ fromRational num
--   --   pure $ Float num'

--   -- GHC.LitDouble num -> do
--   --   let num' = pure $ fromRational num
--   --   pure $ Double num'

--   _ -> throwError ()
