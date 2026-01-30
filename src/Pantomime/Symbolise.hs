{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Symbolise
  ( symbolise
  , symboliseBind
  , symboliseBindMany
  ) where

import GHC.Plugins qualified as GHC
import GHC.Builtin.Types.Prim
  ( intPrimTyCon
  , int8PrimTyCon
  , int16PrimTyCon
  , int32PrimTyCon
  , int64PrimTyCon
  , wordPrimTyCon
  , word8PrimTyCon
  , word16PrimTyCon
  , word32PrimTyCon
  , word64PrimTyCon
  )

import Pantomime.Literal (BuiltInTyCon)
import Pantomime.Expr
import Pantomime.Subst
import Pantomime.Util (foldlBy)
import Pantomime.Binding (FromLitIds (..))

import Grisette (LogicalOp (..), SymBool, mrgIte)

import Control.Arrow (Arrow (..))
import Control.Monad (foldM, unless, join)

import Effectful
import Effectful.Error.Static
import Effectful.GHC.External
import Effectful.Context

symbolise
  :: HasCallStack
  => Error () :> es
  => HasFamInstEnvs :> es
  => Context Reader BuiltInTyCon :> es
  => Context Reader FromLitIds :> es
  => Subst es
  -> GHC.CoreExpr
  -> EvalExpr es
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
      GHC.Lit lit -> symboliseLit subst lit

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

        -- Altough perhaps overly cautious, we check whether the types line up.
        -- This is one of the few places where values are forced and thus one
        -- of the few places where we can perform a sanity check without messing
        -- with the evaluation semantic.
        let expectedTy = substTy subst $ GHC.varType bndr
        scrutTy <- liftEff $ exprType scrut'
        unless (eqType scrutTy expectedTy) do
          throwE ()

        -- TODO: This is a bit ugly now. I guess it handles all the cases, but
        -- it could deserve some cleanup. It somehow feels weird to gather the
        -- scrutinee based on the type like this. Not sure if there is a better
        -- way to do so though. Also, the way we wrap the spine into multiple
        -- 'Either's feels kind of dirty.
        (spine, args) <- if
          | isPrimType expectedTy -> pure (Left scrut', [])
          | otherwise -> first Right <$> collectScrut scrut'

        -- Extend the substitution with the case binder.
        subst' <- liftEff $ extendSubst subst bndr (pure scrut')

        -- Create if-statement for every alternative.
        foldlBy mkUB alts \acc (GHC.Alt con bndrs rhs) -> do
          eq <- case con of
            GHC.DataAlt dc | Right (Right spine') <- spine -> liftEff do
              eqCon spine' $ mkDataCon @64 dc
            GHC.LitAlt lit | Left spine' <- spine -> do
              symboliseEqLit subst spine' lit
            GHC.DEFAULT -> pure true
            _ -> throwE ()

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
          mrgIte eq branch acc

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
  => Context Reader FromLitIds :> fs
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
  => Context Reader FromLitIds :> fs
  => Subst fs
  -> f GHC.CoreBind
  -> Eff es (Subst fs)
symboliseBindMany = foldM symboliseBind

isPrimType :: Type -> Bool
isPrimType ty = case GHC.splitTyConApp_maybe ty of
  Just (tc, [])
    -> tc == intPrimTyCon
    || tc == int8PrimTyCon
    || tc == int16PrimTyCon
    || tc == int32PrimTyCon
    || tc == int64PrimTyCon
    || tc == wordPrimTyCon
    || tc == word8PrimTyCon
    || tc == word16PrimTyCon
    || tc == word32PrimTyCon
    || tc == word64PrimTyCon
  _ -> False

-- | Create a symbolic value from a literal.
--
-- This will user-defined functions for conversions from symbolic literals to
-- Haskell literals. We do so as the representation of literals is decided by
-- the user. Hence, there is no other way to do the conversion than having a
-- user describe it as well.
symboliseLit
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Context Reader FromLitIds :> es
  => Subst es
  -> GHC.Literal
  -> EvalExpr es
symboliseLit subst lit = do
  -- Gather the identifier for equality.
  FromLitIds { .. } <- liftEff $ get @FromLitIds
  (convertId, lit') <- case lit of
    GHC.LitNumber ty num -> do
      let num' :: Num s => s
          num' = fromInteger num
      case ty of
        -- TODO: The bitvector size should be related to the platform size. As
        -- I'm not sure how to do this on the API end, I'll leave it like this
        -- for now...
        GHC.LitNumInt -> pure (toIntId, BitVec @64 num')
        GHC.LitNumInt8 -> pure (toInt8Id, BitVec @8 num')
        GHC.LitNumInt16 -> pure (toInt16Id, BitVec @16 num')
        GHC.LitNumInt32 -> pure (toInt32Id, BitVec @32 num')
        GHC.LitNumInt64 -> pure (toInt64Id, BitVec @64 num')
        GHC.LitNumWord -> pure (toWordId, BitVec @64 num')
        GHC.LitNumWord8 -> pure (toWord8Id, BitVec @8 num')
        GHC.LitNumWord16 -> pure (toWord16Id, BitVec @16 num')
        GHC.LitNumWord32 -> pure (toWord32Id, BitVec @32 num')
        GHC.LitNumWord64 -> pure (toWord64Id, BitVec @64 num')
        GHC.LitNumBigNat -> throwE ()
    _ -> throwE ()

  -- Lookup the equality function.
  convert <- join . failWithE () $ lookupIdSubst subst convertId

  mkApps convert [pure $ mkLit lit']

-- | Create a symbolic equaltiy check between a scrutinee and a literal.
--
-- Like 'symboliseLit', this will use user-defined functions for the equality
-- check, as the representation of literals is also user-defined.
symboliseEqLit
  :: HasCallStack
  => Error () :> es
  => Context Reader FromLitIds :> es
  => Context Reader BuiltInTyCon :> es
  => Subst es
  -> Expr es
  -> GHC.Literal
  -> Eval es SymBool
symboliseEqLit subst lhs rhs = do
  -- Gather the identifier for equality.
  FromLitIds { .. } <- liftEff $ get @FromLitIds
  eqId <- case rhs of
    GHC.LitNumber ty _ -> case ty of
      GHC.LitNumInt -> pure eqIntId
      GHC.LitNumInt8 -> pure eqInt8Id
      GHC.LitNumInt16 -> pure eqInt16Id
      GHC.LitNumInt32 -> pure eqInt32Id
      GHC.LitNumInt64 -> pure eqInt64Id
      GHC.LitNumWord -> pure eqWordId
      GHC.LitNumWord8 -> pure eqWord8Id
      GHC.LitNumWord16 -> pure eqWord16Id
      GHC.LitNumWord32 -> pure eqWord32Id
      GHC.LitNumWord64 -> pure eqWord64Id
      GHC.LitNumBigNat -> throwE ()
    _ -> throwE ()

  -- Lookup the equality function.
  eq <- join . failWithE () $ lookupIdSubst subst eqId

  -- Call the equality function and uwrap the boolean result.
  result <- mkApps eq [pure lhs, symboliseLit subst rhs]
  case result of
    Lit (Bool result') -> pure result'
    _ -> throwE ()
