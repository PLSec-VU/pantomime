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

  , ADT (..)
  , adtType
  , adtFromDataCon
  , adtIsDataCon
  , adtDataConFields

  , Tag
  , dataConToTag
  , tagToDataCon

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
import Grisette.Unified (EvalModeTag (..), GetIntN)
import Grisette.Lib.Control.Monad.Except (mrgThrowError)
import Grisette
  ( Solvable (..)
  , Mergeable
  , Function (..)
  , LogicalOp (..)
  , SymOrd (..)
  , indexed, SymEq (..)
  )

import Data.List ((!?))
import Data.Foldable (find)

import Control.Monad (foldM, unless, forM, guard)
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
  Data :: ADT m ws -> Value m ws
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

instance (MonadEval m, KnownWordSize ws) => StrictIte m (Value m ws) where
  strictIte cond = curry $ \case
    (Primitive lhs, Primitive rhs) -> Primitive <$> strictIte cond lhs rhs
    (Poly lty lhs, Poly rty rhs) -> do
      unless (lty `eqType` rty) $ throwError IllTyped
      Poly lty <$> strictIte cond lhs rhs
    (Data lhs, Data rhs) -> Data <$> strictIte cond lhs rhs
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

-- TODO: We removed strong equivalence now, pehaps this shouldn't be called weak
-- equivalence anymore! Also, I think it would be better if this would return a
-- Constrained SymBool, where Constrained is ExceptT Union Invalid. It seems to
-- me like it would be much better to split the runtime errors from Invalid.
instance (MonadEval m, KnownWordSize ws) => WeakEq m (Value m ws) where
  weakEq = curry $ \case
    (Primitive lhs, Primitive rhs) -> weakEq lhs rhs
    (Data lhs, Data rhs) -> weakEq lhs rhs
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

    (Ty lhs, Ty rhs) -> pure . con $ lhs `eqType` rhs
    (Co lhs, Co rhs) -> pure . con $ lhs `eqCoercion` rhs
    _ -> throwError IllTyped

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
-- TODO: Instead of having one giant guard, wouldn't it be better to make a
-- separate function for each instance? We can write top level functions by
-- putting them in a list and trying until there is a hit. catchError can be
-- used to continuously probe and try the next one when hitting UnsupportedExpr.
-- The same holds for all the other types of functions like this! I guess like
-- the function above says, we really just need to add a Maybe for return. We
-- only return IllTyped when nested values occur. I think we can actually
-- capture this idea in a typeclass (perhaps called symbolise), which takes a
-- Type and returns itself (if possible).
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
    -- TODO: I don't really like this tag creation. Should the tagInRange
    -- maybe just return the condition?
    let tag = tagInRange value tyCon

    let adt = ADT
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
      unless (adtType adt `eqType` argTy) $ throwError IllTyped

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
    Fun iArgTy' _ -> do
      -- TODO: I guess this check is not really necessary if we check types on
      -- function application.
      unless (iArgTy `eqType` iArgTy') $ throwError IllTyped
      error "TODO!"

      -- -- First, create an identifier that represents the function argument.
      -- idx <- freshIdx
      -- let argIdent :: forall t. Solvable (ConType t) t => RuntimeValue S t
      --     argIdent = pure . sym $ indexed "!FUN" idx

      -- -- Then we get an equivalence statement between this fresh argument and the
      -- -- one we actually received as input.
      -- arg' <- typedValue argIdent argTy
      -- eq <- strongEq arg arg'

      -- -- Now, we can use the fresh identifier as function argument for the final
      -- -- value. Note that we are required to do it in this roundabout way, as
      -- -- functions do not always carry an identifier (and it is in general not
      -- -- extractable).
      -- let untyped :: forall t. Interpretable (Ident S -~> t) => RuntimeValue S t
      --     untyped = do
      --       let apply = sym name :: Ident S -~> Ident S -~> t
      --       liftApply apply ident argIdent

      -- -- The actual result of the computation, assuming the equivalence of the
      -- -- input and the fresh identifier.
      -- assume eq <$> typedValue untyped resTy

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

data ADT m ws where
  ADT ::
    { adtTyCon :: TyCon
    , adtTyArgs :: [Type]
    , adtTag :: Tag S ws
    , adtFields :: [[Value m ws]]
    } -> ADT m ws

instance KnownWordSize ws => Outputable (ADT m ws) where
  ppr = ppr . adtType

instance KnownWordSize ws => Assume (ADT m ws) where
  assume cond adt = adt { adtTag = assume cond $ adtTag adt }

instance (MonadEval m, KnownWordSize ws) => StrictIte m (ADT m ws) where
  strictIte cond lhs rhs = do
    unless (adtType lhs `eqType` adtType rhs) $ throwError IllTyped

    -- If-then-else both the tag and the fields.
    tag <- strictIte cond (adtTag lhs) (adtTag rhs)
    fields' <- zipFieldsWith (strictIte cond) lhs rhs

    pure lhs
      { adtTag = tag
      , adtFields = fields'
      }

instance (MonadEval m, KnownWordSize ws) => WeakEq m (ADT m ws) where
  weakEq lhs rhs = do
    unless (adtType lhs `eqType` adtType rhs) $ throwError IllTyped

    -- Ensure the tags are equivalent.
    tagEq <- weakEq (adtTag lhs) (adtTag rhs)

    -- First join all fields in pairs. I.e. for every DataCon, we pair all
    -- fields.
    joint <- zipFieldsWith weakEq lhs rhs

    -- Gather the field equalities for each DataCon.
    fieldEq <- forM (zip [0..] joint) $ \(tag, eqs) -> do
      -- Both tags match the DataCon. We check for both, as we might collapse
      -- some branches if one of them does not match.
      isTag <- do
        l <- weakEq (adtTag lhs) $ pure (con tag)
        r <- weakEq (adtTag rhs) $ pure (con tag)
        pure $ l .&& r

      -- All fields are equal.
      let fieldEq = foldl' (.&&) true eqs

      -- The fields should be equal given that the tag matches.
      pure $ symImplies isTag fieldEq

    -- The tags should be equivalent and the fields of the matching DataCon
    -- should be equivalent.
    pure $ foldl' (.&&) tagEq fieldEq

-- | Get the Type of an ADT.
adtType :: ADT m ws -> Type
adtType adt = mkTyConApp (adtTyCon adt) (adtTyArgs adt)

-- | Create an ADT that matches the given DataCon.
--
-- The Type arguments are the universal quantifier instances of the TyCon.
-- The Value arguments are the fields that match the given DataCon.
adtFromDataCon
  :: KnownWordSize ws
  => MonadEval m
  => DataCon
  -> [Type]
  -> [Value m ws]
  -> m (ADT m ws)
adtFromDataCon dataCon tyArgs fields = do
  -- Get the TyCon for this ADT.
  let tyCon = dataConTyCon dataCon

  -- Gather all DataCons for populating the ADT.
  dataCons <- whyFail IllTyped $ tyConDataCons_maybe tyCon

  -- Populate the remaining fields with fresh values.
  fields' <- forM dataCons $ \dataCon' -> if
    | dataCon == dataCon' -> pure fields
    | otherwise -> freshDataConBndrs dataCon' tyArgs

  pure ADT
    { adtTyCon = tyCon
    , adtTyArgs = tyArgs
    , adtTag = pure $ dataConToTag dataCon
    , adtFields = fields'
    }

-- | Zip the fields of two ADTs.
--
-- Note, this does not check whether the ADTs are of the same type.
zipFieldsWith
  :: Monad m
  => (Value m ws -> Value m ws -> m a)
  -> ADT m ws
  -> ADT m ws
  -> m [[a]]
zipFieldsWith f lhs rhs = do
  let outer = zip (adtFields lhs) (adtFields rhs)
  let inner = sequence . uncurry (zipWith f) <$> outer
  sequence inner

-- | Whether the tag of this ADT is equivalent to the DataCon.
adtIsDataCon
  :: KnownWordSize ws
  => ADT m ws
  -> DataCon
  -> RuntimeValue S SymBool
adtIsDataCon adt dataCon = do
  let tag = dataConToTag dataCon
  (.== con tag) <$> adtTag adt

-- | Get the fields of the ADT that match the DataCon.
--
-- Throws an error if the DataCon does not match the ADT.
adtDataConFields
  :: forall m ws
   . KnownWordSize ws
  => ADT m ws
  -> DataCon
  -> Maybe [Value m ws]
adtDataConFields adt dataCon = do
  guard $ adtTyCon adt == dataConTyCon dataCon
  let tag = dataConToTag @C @ws dataCon
  adtFields adt !? fromIntegral tag

type Tag mode ws = RuntimeValue mode (GetIntN mode (WordBits ws))

-- | Convert a DataCon into an SMT solvable Tag.
dataConToTag
  :: Num (GetIntN mode (WordBits ws))
  => DataCon
  -- TODO: I really want to return a Tag here, but it is a bit ugly... That is,
  -- the tag doesn't need to be in the monad in this instance.
  -> GetIntN mode (WordBits ws)
dataConToTag = fromIntegral . dataConTagZ

-- | Get the DataCon from a Tag and the Type that should match the .
tagToDataCon
  :: forall ws
   . KnownWordSize ws
  => IntN (WordBits ws)
  -> TyCon
  -> Maybe DataCon
tagToDataCon tag tyCon = do
  dataCons <- tyConDataCons_maybe tyCon
  let cmp = (tag ==) . fromIntegral . dataConTagZ
  find cmp dataCons

-- | Add an assertion to a tag that says it's in range.
--
-- I.e. it can only be one of DataCon, and not some undefined value.
tagInRange
  :: KnownWordSize ws
  => Tag S ws
  -> TyCon
  -> Tag S ws
tagInRange tag tyCon = do
  tag' <- tag
  let amount = length $ tyConDataCons tyCon
  -- TODO: Once Grisette adds support for (.&&), we could parameterise on the
  -- evaluation mode. We could of course implement this (.&&) ourselves already,
  -- but we leave it for now.
  let cond =  0 .<= tag' .&& tag' .< fromIntegral amount
  assume cond $ pure tag'

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

instance (MonadEval m, KnownWordSize ws) => WeakEq m (Primitive ws) where
  weakEq = curry $ \case
    (Int lhs, Int rhs) -> weakEq lhs rhs
    (Int8 lhs, Int8 rhs) -> weakEq lhs rhs
    (Int16 lhs, Int16 rhs) -> weakEq lhs rhs
    (Int32 lhs, Int32 rhs) -> weakEq lhs rhs
    (Int64 lhs, Int64 rhs) -> weakEq lhs rhs
    (Word lhs, Word rhs) -> weakEq lhs rhs
    (Word8 lhs, Word8 rhs) -> weakEq lhs rhs
    (Word16 lhs, Word16 rhs) -> weakEq lhs rhs
    (Word32 lhs, Word32 rhs) -> weakEq lhs rhs
    (Word64 lhs, Word64 rhs) -> weakEq lhs rhs
    (Float lhs, Float rhs) -> weakEq lhs rhs
    (Double lhs, Double rhs) -> weakEq lhs rhs
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
