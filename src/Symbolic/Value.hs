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
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE FunctionalDependencies #-}

module Symbolic.Value
  ( Value (..)
  , mkCast'

  , typedValue
  , freshValue
  , invalidValue

  , nArity

  , applyValue
  , applyValues

  , ADT' (..)

  , Primitive (..)
  , typedPrimitive
  ) where

import GHC.Plugins hiding (empty)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.TyCo.Rep (scaledThing, Coercion (..))
import GHC.Core.Type (substTy)
import GHC.Core.TyCo.FVs (shallowTyCoVarsOfType)
import GHC.Core.Coercion.Opt
import GHC.Builtin.Types.Prim
import GHC.Tc.Utils.TcType (hasTyVarHead)
import GHC.Platform (PlatformWordSize)

import Grisette.SymPrim
import Grisette.Unified (EvalModeTag (..))
import Grisette.Lib.Control.Monad.Except (mrgThrowError)
import Grisette.Internal.SymPrim.Prim.Term (SupportedNonFuncPrim)
import Grisette
  ( Solvable (..)
  , Mergeable
  , Function (..)
  , Symbol
  , SymEq (..)
  , SymbolSetRep (..)
  , indexed
  , LogicalOp (..), SymOrd (..), SimpleMergeable (..)
  )

import Control.Monad (foldM, unless, forM)
import Control.Monad.Except (MonadError (..))

import Symbolic.Util
import Symbolic.WordSize
import Symbolic.Runtime
import Symbolic.Identifier
import Symbolic.MonadEval

-- TODO: Add comment to what this data type is!
data Value m ws where
  Primitive :: Primitive ws -> Value m ws
  Poly :: Type -> RuntimeValue S (Ident S) -> Value m ws
  Data :: ADT' m ws -> Value m ws
  -- TODO: I don't really like the prime on the name of Cast here. Maybe we
  -- could go for some other name? Perhaps just Newtype, as that's pretty much
  -- what we wrap in there anyway. The alternative would be to just prefix all
  -- options with something like 'V'. Then we can also use VType instead of Ty,
  -- VLam instead of Fun, etc.
  Cast' :: Coercion -> Value m ws -> Value m ws
  Fun :: Kind  -> (Value m ws -> m (Value m ws)) -> Value m ws
  Ty :: Type -> Value m ws
  Co :: Coercion -> Value m ws

instance KnownWordSize ws => Outputable (Value m ws) where
  ppr = \case
    Primitive prim -> ppr prim
    Poly ty _ -> ppr ty
    Data adt -> ppr adt
    Cast' co val -> ppr val <+> "<->" <+> ppr (coercionKindRole co)
    Fun argTy _ -> ppr argTy <+> "-> ?"
    Ty ty -> text "@" <+> ppr ty
    Co co -> ppr co

instance (MonadEval m, KnownWordSize ws) => StrongEq m (Value m ws) where
  strongEq = curry $ \case
    (Primitive lhs, Primitive rhs) -> strongEq lhs rhs
    (Poly lty lhs, Poly rty rhs) -> do
      unless (lty `eqType` rty) $ throwError IllTyped
      strongEq lhs rhs

    (Cast' lco lhs, Cast' rco rhs) -> do
      unless (lco `eqCoercion` rco) $ throwError IllTyped
      strongEq lhs rhs

    (Fun lty lhs, Fun rty rhs) -> do
      -- TODO: Comment this thing!
      unless (lty `eqType` rty) $ throwError IllTyped
      idx <- freshIdx
      let symbol = indexed "!qarg" idx
      let untyped :: forall t. Solvable (ConType t) t => RuntimeValue S t
          untyped = pure $ sym symbol
      arg <- typedValue untyped lty

      lhs' <- lhs arg
      rhs' <- rhs arg
      eq <- strongEq lhs' rhs'

      -- FIXME: This equivalence we are building is absolutely terrible. It's
      -- huge and capturates way too many variables that we do not require...
      typed <- valueSymbol @m @ws symbol lty
      let quantifier = buildSymbolSet typed
      pure $ forallSet quantifier eq

    (Ty lhs, Ty rhs) -> pure . con $ lhs `eqType` rhs
    (Co lhs, Co rhs) -> pure . con $ lhs `eqCoercion` rhs
    _ -> throwError IllTyped

instance (MonadEval m, KnownWordSize ws) => StrictIte m (Value m ws) where
  strictIte cond = curry $ \case
    (Primitive lhs, Primitive rhs) -> Primitive <$> strictIte cond lhs rhs
    (Poly lty lhs, Poly rty rhs) -> do
      unless (lty `eqType` rty) $ throwError IllTyped
      Poly lty <$> strictIte cond lhs rhs
    (Data lhs, Data rhs) -> do
      unless (adtType' lhs `eqType` adtType' rhs) $ throwError IllTyped

      -- TODO: Make this nicer!
      tag <- strictIte cond (adtTag lhs) (adtTag rhs)
      let allPairs = uncurry zip <$> zip (adtFields lhs) (adtFields rhs)
      fields' <- forM allPairs $ \pairs -> do
        forM pairs $ uncurry (strictIte cond)
      pure $ Data lhs
        { adtTag = tag
        , adtFields = fields'
        }

    (Cast' lco lhs, Cast' rco rhs) -> do
      unless (lco `eqCoercion` rco) $ throwError IllTyped
      result <- strictIte cond lhs rhs
      pure $ Cast' lco result
    (Fun larg lhs, Fun rarg rhs) -> do
      unless (larg `eqType` rarg) $ throwError IllTyped
      pure . Fun larg $ \arg -> do
        lhs' <- lhs arg
        rhs' <- rhs arg
        strictIte cond lhs' rhs'
    (Ty _, Ty _) -> throwError UnsupportedExpr
    (Co _, Co _) -> throwError UnsupportedExpr
    _ -> throwError IllTyped

instance (MonadEval m, KnownWordSize ws) => Assume (Value m ws) where
  assume cond = \case
    Primitive prim -> Primitive $ assume cond prim
    Poly ty value -> Poly ty $ assume cond value
    Data adt -> Data $ assume cond adt
    Cast' co val -> Cast' co $ assume cond val
    Fun argTy fun -> do
      Fun argTy $ \arg -> do
        assume cond <$> fun arg
    -- TODO: I guess there is nothing to assume in these cases. Still this seems
    -- like it could introduce some unexpected behaviour if we're not careful.
    -- I think we should change this. We shouldn't just drop assumptions...
    Ty ty -> Ty ty
    Co co -> Co co

-- TODO: Explain why we distinguish between strong and weak equality.
instance (MonadEval m, KnownWordSize ws) => WeakEq m (Value m ws) where
  weakEq = curry $ \case
    -- TODO: Clean this up and comment it!
    (Data lhs, Data rhs) -> do
      unless (adtType' lhs `eqType` adtType' rhs) $ throwError IllTyped
      tagEq <- weakEq (adtTag lhs) (adtTag rhs)
      let pairs = uncurry zip <$> zip (adtFields lhs) (adtFields rhs)
      fieldEq <- forM (zip [0..] pairs) $ \(tag, fields) -> do
        eqs <- forM fields $ uncurry weakEq
        let eqs' = foldl' (.&&) true eqs
        isTag <- do
          l <- weakEq (adtTag lhs) $ pure (con tag)
          r <- weakEq (adtTag rhs) $ pure (con tag)
          pure $ l .&& r

        pure $ symImplies isTag eqs'

      pure $ foldl' (.&&) tagEq fieldEq

    (Cast' lco lhs, Cast' rco rhs) -> do
      unless (lco `eqCoercion` rco) $ throwError IllTyped
      weakEq lhs rhs

    (Fun lty lhs, Fun rty rhs) -> do
      unless (lty `eqType` rty) $ throwError IllTyped
      arg <- freshValue lty
      lhs' <- lhs arg
      rhs' <- rhs arg
      weakEq lhs' rhs'

    (Poly lty lhs, Poly rty rhs) -> do
      unless (lty `eqType` rty) $ throwError IllTyped
      weakEq lhs rhs

    -- The remaining cases do not distinguish between weak and strong equivalence.
    -- TODO: I think I want to individually implement weakEq for Primitive and
    -- call that instead. That seems better to me!
    -- FIXME: I don't actually think the strongEq is the same as weakEq for
    -- primitives!
    (lhs, rhs) -> strongEq lhs rhs

-- | Create a cast.
--
-- Merges nested casts. This should always be preferred over manually creating
-- a cast.
mkCast'
  -- :: MonadError EvalError m
  :: MonadEval m
  => KnownWordSize ws
  => Coercion
  -> Value m ws
  -> m (Value m ws)
mkCast' c v = case (optCoercion' c, v) of
  (co@ForAllCo { fco_kind }, Fun argTy fun) -> do
    let argTy' = coercionRKind fco_kind
    unless (argTy `eqType` coercionLKind fco_kind) $ throwError IllTyped

    pure . Fun argTy' $ \case
      Ty arg -> do
        let arg' = mkCastTy arg $ SymCo fco_kind
        result <- fun $ Ty arg'
        let resCo = mkInstCo co $ mkNomReflCo arg'
        mkCast' resCo result
      _ -> throwError IllTyped

  (FunCo { fco_arg, fco_res }, Fun argTy fun) -> do
    let argTy' = coercionRKind fco_arg
    unless (argTy `eqType` coercionLKind fco_arg) $ throwError IllTyped

    pure . Fun argTy' $ \arg -> do
      arg' <- mkCast' (SymCo fco_arg) arg
      result <- fun arg'
      mkCast' fco_res result

  (co, Cast' co' value) -> do
    -- TODO: Check whether the casts actually can be transitively applied.
    let trans = mkTransCo co' co
    mkCast' trans value

  -- TODO: Check whether the coercion actually fits the value.
  (co, value)
    | isReflexiveCo co -> pure value
    | otherwise -> pure $ Cast' co value
  where
    optCoercion' = optCoercion (OptCoercionOpts True) emptySubst

-- | Constraints for creating the symbolic values we require.
--
-- These constraints are picked such that we can avoid overlapping instances
-- whilst allowing all values we require to be constructed.
-- TODO: Should we place the interpretable constraints into the
-- Identifier file? Then we can use interpretWith in places where we currently
-- are not. We have a bit of code duplication in some places rn, so maybe that
-- would resolve some of that!
type Symbolisable t ws =
  ( Mergeable t
  , LinkedRep (ConType t) t
  , Solvable (ConType t) t
  , Interpretable t
  , Interpretable (SymIntN (WordBits ws) -~> t)
  , Interpretable (SymIntN8 -~> t)
  , Interpretable (SymIntN16 -~> t)
  , Interpretable (SymIntN32 -~> t)
  , Interpretable (SymIntN64 -~> t)
  , Interpretable (SymWordN (WordBits ws) -~> t)
  , Interpretable (SymWordN8 -~> t)
  , Interpretable (SymWordN16 -~> t)
  , Interpretable (SymWordN32 -~> t)
  , Interpretable (SymWordN64 -~> t)
  , Interpretable (SymFP32 -~> t)
  , Interpretable (SymFP64 -~> t)
  )

-- TODO: I guess this should just return a maybe, as there is only one reason
-- why this would possibly fail.
typedValue
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  -- TODO: I think with the new setup this is way to general of a thing to want?
  -- I think at this point, we just want to eliminitate this argument entirely
  -- and just assume some stuff on a value afterwards if required no?
  => (forall t. Symbolisable t ws => RuntimeValue S t)
  -> Type
  -> m (Value m ws)
typedValue value ty
  | Right prim <- typedPrimitive value ty = pure $ Primitive prim

  | Just (tyCon, tys) <- tcSplitTyConApp_maybe ty
  , Just (ty', co) <- instNewTyCon_maybe tyCon tys = do
    value' <- typedValue value ty'
    let co' = mkSymCo co
    mkCast' co' value'

  | Just (tyCon, tyArgs) <- tcSplitTyConApp_maybe ty
  , isDataTyCon tyCon
  , Just dataCons <- tyConDataCons_maybe tyCon = do
    -- TODO: This will loop infinitely for recursive types. We need to resolve
    -- that somehow.

    -- Create fresh values for all fields.
    fields <- forM dataCons $ flip freshDataConBndrs tyArgs
    let tag = do
          let amount = length $ tyConDataCons tyCon
          value' <- value @(SymIntN (WordBits ws))
          -- TODO: Once Grisette adds support for (.&&), we could parameterise on the
          -- evaluation mode. We could of course implement this (.&&) ourselves already,
          -- but we leave it for now.
          let cond =  0 .<= value' .&& value' .< fromIntegral amount
          mrgIte cond (pure value') (throwError Invalid)

    let adt = ADT'
          { adtTyCon = tyCon
          , adtTyArgs = tyArgs
          , adtTag = tag
          , adtFields = fields
          }
    pure $ Data adt

  | Just (_, _, argTy, resTy) <- splitFunTy_maybe ty = do
    typedLambda value argTy resTy

  | Just (tyCoVar, resTy) <- splitForAllTyCoVar_maybe ty = do
    let vars = shallowTyCoVarsOfType ty
    let subst = mkEmptySubst $ InScope vars

    let argKind = tyVarKind tyCoVar
    -- TODO: This should not be a function accepting both a coercion variable or
    -- type variable. Instead, two individual functions should be made for each
    -- case.
    pure . Fun argKind $ \case
      Ty arg -> do
        let subst' = extendTvSubst subst tyCoVar arg
        let resTy' = substTy subst' resTy
        typedValue value resTy'

      Co arg -> do
        let subst' = extendCvSubst subst tyCoVar arg
        let resTy' = substTy subst' resTy
        typedValue value resTy'

      _ -> throwError IllTyped

  -- TODO: Is this correct? My guess is that any type variable should do.
  | isTypeLikeKind ty = pure $ Ty alphaTy

  | hasTyVarHead ty = pure $ Poly ty value

  | otherwise = throwError UnsupportedExpr

-- | Create a uninterpreted lambda of the given type.
--
-- TODO: Can't we make this function a little bit smaller?
--
-- Yes, this function is big. This has everything to do with overlapping
-- instances on SupportedPrim.
--
-- I.e. a, (a -~> b) and (a -~> (b -~> c)) all overlap and have separate
-- instances. To get a symbolic value for these, we need to know the instance
-- concretely. I did some trickery to not have to write this for every product
-- via 'typedValue' and its constraints. Still we get this abominable
-- duplication because we explicitely need to spell out each instance.
typedLambda
  :: forall m ws
   . KnownWordSize ws
  => MonadEval m
  => RuntimeValue S (Ident S)
  -> Type
  -> Type
  -> m (Value m ws)
typedLambda ident argTy resTy = if
  | eqArg intPrimTy -> lam $ \case
    Primitive (Int arg) -> do
      let untyped :: forall t. Interpretable (SymIntN (WordBits ws) -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> SymIntN (WordBits ws) -~> t
            liftApply apply ident arg

      typedValue untyped resTy
    _ -> throwError IllTyped

  | eqArg int8PrimTy -> lam $ \case
    Primitive (Int8 arg) -> do
      let untyped :: forall t. Interpretable (SymIntN8 -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> SymIntN8 -~> t
            liftApply apply ident arg

      typedValue untyped resTy
    _ -> throwError IllTyped

  | eqArg int16PrimTy -> lam $ \case
    Primitive (Int16 arg) -> do
      let untyped :: forall t. Interpretable (SymIntN16 -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> SymIntN16 -~> t
            liftApply apply ident arg

      typedValue untyped resTy
    _ -> throwError IllTyped

  | eqArg int32PrimTy -> lam $ \case
    Primitive (Int32 arg) -> do
      let untyped :: forall t. Interpretable (SymIntN32 -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> SymIntN32 -~> t
            liftApply apply ident arg

      typedValue untyped resTy
    _ -> throwError IllTyped

  | eqArg int64PrimTy -> lam $ \case
    Primitive (Int64 arg) -> do
      let untyped :: forall t. Interpretable (SymIntN64 -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> SymIntN64 -~> t
            liftApply apply ident arg

      typedValue untyped resTy
    _ -> throwError IllTyped

  | eqArg wordPrimTy -> lam $ \case
    Primitive (Word arg) -> do
      let untyped :: forall t. Interpretable (SymWordN (WordBits ws) -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> SymWordN (WordBits ws) -~> t
            liftApply apply ident arg

      typedValue untyped resTy
    _ -> throwError IllTyped

  | eqArg word8PrimTy -> lam $ \case
    Primitive (Word8 arg) -> do
      let untyped :: forall t. Interpretable (SymWordN8 -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> SymWordN8 -~> t
            liftApply apply ident arg

      typedValue untyped resTy
    _ -> throwError IllTyped

  | eqArg word16PrimTy -> lam $ \case
    Primitive (Word16 arg) -> do
      let untyped :: forall t. Interpretable (SymWordN16 -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> SymWordN16 -~> t
            liftApply apply ident arg

      typedValue untyped resTy
    _ -> throwError IllTyped

  | eqArg word32PrimTy -> lam $ \case
    Primitive (Word32 arg) -> do
      let untyped :: forall t. Interpretable (SymWordN32 -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> SymWordN32 -~> t
            liftApply apply ident arg

      typedValue untyped resTy
    _ -> throwError IllTyped

  | eqArg word64PrimTy -> lam $ \case
    Primitive (Word64 arg) -> do
      let untyped :: forall t. Interpretable (SymWordN64 -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> SymWordN64 -~> t
            liftApply apply ident arg

      typedValue untyped resTy
    _ -> throwError IllTyped

  | eqArg floatPrimTy -> lam $ \case
    Primitive (Float arg) -> do
      let untyped :: forall t. Interpretable (SymFP32 -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> SymFP32 -~> t
            liftApply apply ident arg

      typedValue untyped resTy
    _ -> throwError IllTyped

  | eqArg doublePrimTy -> lam $ \case
    Primitive (Double arg) -> do
      let untyped :: forall t. Interpretable (SymFP64 -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> SymFP64 -~> t
            liftApply apply ident arg

      typedValue untyped resTy
    _ -> throwError IllTyped

  | Just (tyCon, _) <- tcSplitTyConApp_maybe argTy
  , isDataTyCon tyCon -> lam $ \case
    Data adt -> do
      -- TODO: I guess this check is not really necessary if we check types on
      -- function application.
      unless (adtType' adt `eqType` argTy) $ throwError IllTyped

      error "TODO!"
      -- let untyped :: forall t. Interpretable (Ident S -~> t) => RuntimeValue S t
      --     untyped = do
      --       let apply = sym name :: Ident S -~> Ident S -~> t
      --       liftApply apply ident arg

      -- typedValue untyped resTy
    _ -> throwError IllTyped

  | Just (tyCon, tys) <- tcSplitTyConApp_maybe argTy
  , Just (argTy', co) <- instNewTyCon_maybe tyCon tys -> lam $ \case
    Cast' co' arg -> do
      -- TODO: I guess this check is not really necessary if we check types on
      -- function application.
      unless (co `eqCoercion` SymCo co') $ throwError IllTyped
      fun <- typedLambda ident argTy' resTy
      applyValue fun arg
    _ -> throwError IllTyped

  | hasTyVarHead argTy -> lam $ \case
    Poly ty poly -> do
      -- TODO: I guess this check is not really necessary if we check types on
      -- function application.
      unless (ty `eqType` argTy) $ throwError IllTyped

      let untyped :: forall t. Interpretable (Ident S -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> Ident S -~> t
            liftApply apply ident poly

      typedValue untyped resTy
    _ -> throwError IllTyped

  | Just (_, _, iArgTy, _) <- splitFunTy_maybe argTy -> lam $ \case
    arg@(Fun iArgTy' _) -> do
      -- TODO: I guess this check is not really necessary if we check types on
      -- function application.
      unless (iArgTy `eqType` iArgTy') $ throwError IllTyped

      -- First, create an identifier that represents the function argument.
      idx <- freshIdx
      let argIdent :: forall t. Solvable (ConType t) t => RuntimeValue S t
          argIdent = pure . sym $ indexed "!FUN" idx

      -- Then we get an equivalence statement between this fresh argument and the
      -- one we actually received as input.
      arg' <- typedValue argIdent argTy
      eq <- strongEq arg arg'

      -- Now, we can use the fresh identifier as function argument for the final
      -- value. Note that we are required to do it in this roundabout way, as
      -- functions do not always carry an identifier (and it is in general not
      -- extractable).
      let untyped :: forall t. Interpretable (Ident S -~> t) => RuntimeValue S t
          untyped = do
            let apply = sym name :: Ident S -~> Ident S -~> t
            liftApply apply ident argIdent

      -- The actual result of the computation, assuming the equivalence of the
      -- input and the fresh identifier.
      assume eq <$> typedValue untyped resTy

    _ -> throwError IllTyped

  | otherwise -> throwError UnsupportedExpr
  where
    lam = pure . Fun argTy
    eqArg = eqType argTy
    liftApply apply = liftA2 $ \a0 a1 -> apply # a0 # a1
    -- TODO: I think we should make a separate file/spot with all the
    -- non-indexed names. It is very messy and error prone to define global
    -- names all over the place.
    name = "!apply"

-- TODO: I really should elaborate on this (and why we need it).
valueSymbol
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => Symbol
  -> Type
  -> m SomeTypedConstantSymbol
valueSymbol symbol ty
  | Right prim <- primitiveSymbol @_ @ws symbol ty = pure prim
  | Just (tyCon, tys) <- tcSplitTyConApp_maybe ty
  , Just (ty', _) <- instNewTyCon_maybe tyCon tys = do
    valueSymbol @m @ws symbol ty'
  | Just (tyCon, _) <- tcSplitTyConApp_maybe ty
  , isDataTyCon tyCon = symbol' @(Ident C)
  | Just (_, _, _, _) <- splitFunTy_maybe ty = symbol' @(Ident C)
  | isTyVarTy ty = symbol' @(Ident C)
  | Just _ <- splitTyConApp_maybe ty = symbol' @(Ident C)
  | otherwise = throwError UnsupportedExpr
  where
    symbol' :: forall t. SupportedNonFuncPrim t => m SomeTypedConstantSymbol
    symbol' = pure $ SomeTypedSymbol (typedConstantSymbol @t symbol)

-- | Create an unconstrained, typed value.
freshValue
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => Type
  -> m (Value m ws)
freshValue ty = do
  idx <- freshIdx
  let untyped :: forall t. Solvable (ConType t) t => RuntimeValue S t
      untyped = pure . sym $ indexed "!fresh" idx
  typedValue untyped ty

-- | Create fresh binders for the given DataCon.
--
-- Note the type arguments will instantiate the universal quantifiers of the
-- DataCon. They in general do not correspond to the types of the binders.
freshDataConBndrs
  :: MonadEval m
  => KnownWordSize ws
  => DataCon
  -> [Type]
  -> m [Value m ws]
freshDataConBndrs dataCon tyArgs = do
  let fieldTys = scaledThing <$> dataConInstArgTys dataCon tyArgs
  forM fieldTys freshValue

-- | A value that should not be reachable.
--
-- It will be typed according to the given core type.
invalidValue 
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => Type
  -> m (Value m ws)
invalidValue = typedValue $ mrgThrowError Invalid

-- | Create a function with the arity of whatever we are folding over.
--
-- Use the accumulation function to pass data to the root value of the function.
-- We do it in this way as we cannot just pass values into a Haskell lambda.
nArity
  :: forall m t ws a b
   . Monad m
  => Foldable t
  => (b -> m (Value m ws))
  -- ^ Root value and what we accumulate.
  -> t (a, Kind)
  -- ^ What we fold over. Decides the arity of the function.
  -> (b -> a -> Value m ws -> m b)
  -- ^ Accumulation function
  -> m (b -> m (Value m ws))
nArity acc xs f = foldrM' acc xs $ \(x, argTy) acc' -> do
  pure $ \y -> pure . Fun argTy $ \arg -> do
    res <- f y x arg
    acc' res

-- | Apply a function to a value.
--
-- This will fail if the first value is not a function, or if the inner function
-- throws upon receiving the argument.
applyValue
  :: MonadEval m
  => Value m ws
  -> Value m ws
  -> m (Value m ws)
applyValue = curry $ \case
  (Fun _ fun, arg) -> fun arg
  _ -> throwError IllTyped

-- | Apply the given arguments.
--
-- A foldM over a call of 'applyValue'.
applyValues
  :: MonadEval m
  => Value m ws
  -> [Value m ws]
  -> m (Value m ws)
applyValues = foldM applyValue

data ADT' m ws where
  ADT' ::
    { adtTyCon :: TyCon
    , adtTyArgs :: [Type]
    , adtTag :: RuntimeValue S (SymIntN (WordBits ws))
    , adtFields :: [[Value m ws]]
    } -> ADT' m ws

instance KnownWordSize ws => Outputable (ADT' m ws) where
  ppr = ppr . adtType'

instance KnownWordSize ws => Assume (ADT' m ws) where
  assume cond adt = adt { adtTag = assume cond $ adtTag adt }

adtType' :: ADT' m ws -> Type
adtType' adt = mkTyConApp (adtTyCon adt) (adtTyArgs adt)

-- | Primitive values supported by the symbolic solver.
data Primitive (ws :: PlatformWordSize) where
  -- TODO: Add support for Char
  -- TODO: Add support for ByteArray (as this is how big integers are
  -- implemented under the hood).
  -- TODO: Add support for symbolic (higher order) functions.
  -- Char :: RuntimeValue (SymWordN 31) -> Value m n
  -- BigNat :: RuntimeValue SymInteger -> Value m n
  -- TODO: Shouldn't we be using the newtype SymInt we created here? We don't
  -- need to wrap just solvables in RuntimeValue. In fact, RuntimeValue itself
  -- wraps Either, which is non-solvable. I really think it would be best to use
  -- the newtype wrapper here, it is a lot more clear! The same goes for Word
  -- btw.
  Int :: RuntimeValue S (SymIntN (WordBits ws)) -> Primitive ws
  Int8 :: RuntimeValue S SymIntN8 -> Primitive ws
  Int16 :: RuntimeValue S SymIntN16 -> Primitive ws
  Int32 :: RuntimeValue S SymIntN32 -> Primitive ws
  Int64 :: RuntimeValue S SymIntN64 -> Primitive ws
  Word :: RuntimeValue S (SymWordN (WordBits ws)) -> Primitive ws
  Word8 :: RuntimeValue S SymWordN8 -> Primitive ws
  Word16 :: RuntimeValue S SymWordN16 -> Primitive ws
  Word32 :: RuntimeValue S SymWordN32 -> Primitive ws
  Word64 :: RuntimeValue S SymWordN64 -> Primitive ws
  Float :: RuntimeValue S SymFP32 -> Primitive ws
  Double :: RuntimeValue S SymFP64 -> Primitive ws

instance KnownWordSize ws => Outputable (Primitive ws) where
  ppr = \case
    Int _ -> "Int#"
    Int8 _ -> "Int8#"
    Int16 _ -> "Int16#"
    Int32 _ -> "Int32#"
    Int64 _ -> "Int64#"
    Word _ -> "Word#"
    Word8 _ -> "Word8#"
    Word16 _ -> "Word16#"
    Word32 _ -> "Word32#"
    Word64 _ -> "Word64#"
    Float _ -> "Float#"
    Double _ -> "Double#"

instance (MonadEval m, KnownWordSize ws) => StrongEq m (Primitive ws) where
  strongEq = curry $ \case
    (Int lhs, Int rhs) -> pure $ lhs .== rhs
    (Int8 lhs, Int8 rhs) -> pure $ lhs .== rhs
    (Int16 lhs, Int16 rhs) -> pure $ lhs .== rhs
    (Int32 lhs, Int32 rhs) -> pure $ lhs .== rhs
    (Int64 lhs, Int64 rhs) -> pure $ lhs .== rhs
    (Word lhs, Word rhs) -> pure $ lhs .== rhs
    (Word8 lhs, Word8 rhs) -> pure $ lhs .== rhs
    (Word16 lhs, Word16 rhs) -> pure $ lhs .== rhs
    (Word32 lhs, Word32 rhs) -> pure $ lhs .== rhs
    (Word64 lhs, Word64 rhs) -> pure $ lhs .== rhs
    (Float lhs, Float rhs) -> pure $ lhs .== rhs
    (Double lhs, Double rhs) -> pure $ lhs .== rhs
    _ -> throwError IllTyped

instance (MonadEval m, KnownWordSize ws) => StrictIte m (Primitive ws) where
  strictIte cond = curry $ \case
    (Int lhs, Int rhs) -> Int <$> strictIte cond lhs rhs
    (Int8 lhs, Int8 rhs) -> Int8 <$> strictIte cond lhs rhs
    (Int16 lhs, Int16 rhs) -> Int16 <$> strictIte cond lhs rhs
    (Int32 lhs, Int32 rhs) -> Int32 <$> strictIte cond lhs rhs
    (Int64 lhs, Int64 rhs) -> Int64 <$> strictIte cond lhs rhs
    (Word lhs, Word rhs) -> Word <$> strictIte cond lhs rhs
    (Word8 lhs, Word8 rhs) -> Word8 <$> strictIte cond lhs rhs
    (Word16 lhs, Word16 rhs) -> Word16 <$> strictIte cond lhs rhs
    (Word32 lhs, Word32 rhs) -> Word32 <$> strictIte cond lhs rhs
    (Word64 lhs, Word64 rhs) -> Word64 <$> strictIte cond lhs rhs
    (Float lhs, Float rhs) -> Float <$> strictIte cond lhs rhs
    (Double lhs, Double rhs) -> Double <$> strictIte cond lhs rhs
    _ -> throwError IllTyped

instance KnownWordSize ws => Assume (Primitive ws) where
  assume cond = \case
    Int value -> Int $ assume cond value
    Int8 value -> Int8 $ assume cond value
    Int16 value -> Int16 $ assume cond value
    Int32 value -> Int32 $ assume cond value
    Int64 value -> Int64 $ assume cond value
    Word value -> Word $ assume cond value
    Word8 value -> Word8 $ assume cond value
    Word16 value -> Word16 $ assume cond value
    Word32 value -> Word32 $ assume cond value
    Word64 value -> Word64 $ assume cond value
    Float value -> Float $ assume cond value
    Double value -> Double $ assume cond value

-- | Construct a primitive, symbolic value with the given type.
typedPrimitive
  :: forall m ws
   . MonadError EvalError m
  => KnownWordSize ws
  => (forall t. Symbolisable t ws => RuntimeValue S t)
  -> Type
  -> m (Primitive ws)
typedPrimitive value ty
  | ty `eqType` intPrimTy = pure $ Int value
  | ty `eqType` int8PrimTy = pure $ Int8 value
  | ty `eqType` int16PrimTy = pure $ Int16 value
  | ty `eqType` int32PrimTy = pure $ Int32 value
  | ty `eqType` int64PrimTy = pure $ Int64 value
  | ty `eqType` wordPrimTy = pure $ Word value
  | ty `eqType` word8PrimTy = pure $ Word8 value
  | ty `eqType` word16PrimTy = pure $ Word16 value
  | ty `eqType` word32PrimTy = pure $ Word32 value
  | ty `eqType` word64PrimTy = pure $ Word64 value
  | ty `eqType` floatPrimTy = pure $ Float value
  | ty `eqType` doublePrimTy = pure $ Double value
  | otherwise = throwError UnsupportedExpr

primitiveSymbol
  :: forall m ws
   . MonadError EvalError m
  => KnownWordSize ws
  => Symbol
  -> Type
  -> m SomeTypedConstantSymbol
primitiveSymbol symbol ty
  | ty `eqType` intPrimTy = symbol' @(IntN (WordBits ws))
  | ty `eqType` int8PrimTy = symbol' @IntN8
  | ty `eqType` int16PrimTy = symbol' @IntN16
  | ty `eqType` int32PrimTy = symbol' @IntN32
  | ty `eqType` int64PrimTy = symbol' @IntN64
  | ty `eqType` wordPrimTy = symbol' @(WordN (WordBits ws))
  | ty `eqType` word8PrimTy = symbol' @WordN8
  | ty `eqType` word16PrimTy = symbol' @WordN16
  | ty `eqType` word32PrimTy = symbol' @WordN32
  | ty `eqType` word64PrimTy = symbol' @WordN64
  | ty `eqType` floatPrimTy = symbol' @FP32
  | ty `eqType` doublePrimTy = symbol' @FP64
  | otherwise = throwError UnsupportedExpr
  where
    symbol' :: forall t. SupportedNonFuncPrim t => m SomeTypedConstantSymbol
    symbol' = pure $ SomeTypedSymbol (typedConstantSymbol @t symbol)
