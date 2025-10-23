-- TODO: Write a note on why we use marker types instead of the real one.
{-# LANGUAGE DefaultSignatures #-}
module Pantomime.Primitive.Reify
  -- | Reify typeclasses.
  ( CoreType (..)
  , CoreTypeBuiltin (..)
  , Reify (..)
  , ReifyBuiltin
  , builtinReify
  , builtinInterpret

  -- | Lambdas and quantifiers.
  , type (~>)
  , type (+>)
  , RTyVar

  -- | Kinds for type variables.
  , RTyVar_
  , RTypeKind
  , RBoxedRep
  , RLevity

  -- | Pantomime primitives.
  , RIntN

  -- | Haskell primitives.
  , RHIntN
  , RHIntPW
  , RHWordN
  , RHWordPW

  -- | Common Haskell types.
  , RKnownNat
  , RNatural
  , RInteger
  , RBool

  -- | Lifting function for ease of use.
  , liftF1'
  , liftF2
  , liftF2'
  , liftF3
  , liftF3'
  , liftF4
  , liftF4'
  ) where

import Pantomime.Expr
  ( Type
  , Expr (..)
  , Eval
  , Literal (..)
  , mkLam
  , mkType
  , mkApp
  , mkLit
  , mkIntN
  , mkDataCon
  , mkEnumCon
  , mkWordN
  , mkCast
  , collectArgs
  , forceTy
  , exprToBool
  , concreteDataCon
  , exprType
  , throwE
  , failWithE
  , liftR
  )
import Pantomime.Subst
  ( extendSubst
  , substTy
  , mkEmptySubst
  )
import Pantomime.Primitive.Operation qualified as Primitive
import Pantomime.Grisette.BitVector (IntN, WordN)
import Pantomime.Grisette.SomeBV (SomeBV (..))
import Pantomime.Grisette.SizedBV (sizedBVResizeZ)
import Pantomime.Result (type (!>))

import GHC.TypeNats (KnownNat, Nat, natVal)
import GHC.Builtin.Types.Prim
  ( wordPrimTy
  , intPrimTy
  , intPrimTy
  , int8PrimTy
  , int16PrimTy
  , int32PrimTy
  , int64PrimTy
  , wordPrimTy
  , word8PrimTy
  , word16PrimTy
  , word32PrimTy
  , word64PrimTy
  , alphaTyVars
  )
import GHC.Data.Pair (Pair(..))
import GHC.Core.TyCo.Compare (eqType)
import GHC.Plugins qualified as GHC
import GHC.Plugins
  ( Name
  , Kind
  , ForAllTyFlag (..)
  , VarBndr (..)
  , mkTyConApp
  , mkSymCo
  , mkFunTy
  , mkTyVarTy
  , mkForAllTy
  , setTyVarKind
  , splitForAllCoVar_maybe
  , splitFunTy_maybe
  , splitTyConApp_maybe
  , instNewTyCon_maybe
  , coercionKind
  , naturalTy
  , naturalTyCon
  , naturalNSDataCon
  , naturalNBDataCon
  , integerTy
  , integerTyCon
  , integerINDataCon
  , integerISDataCon
  , integerIPDataCon
  , boolTy
  , tYPETyCon
  , levityTy
  , boxedRepDataConTyCon
  , splitForAllTyCoVar_maybe
  , liftedTypeKind
  , getTyVar
  )

import Language.Haskell.TH qualified as TH

import Data.Kind qualified as Kind
import Data.Type.Bool (type (||))
import Data.Type.Equality (type (==))
import Data.Typeable (Proxy(..), type (:~:) (..), eqT)

import Control.Applicative (liftA3)
import Control.Monad (unless)

import Grisette.Unified (EvalModeTag(..))
import Grisette (SymBool, BitCast (..), liftUnion)

import Effectful
import Effectful.Error.Static
import Effectful.GHC.TyThing
import Effectful.GHC.TH
import GHC.Core.TyCo.Rep (LevityType)

-- | Any marker type that represents some type within GHC Core.
class CoreType a where
  coreType
    :: HasCallStack
    => Error (LookupError TH.Name) :> es
    => Error (LookupError Name) :> es
    => HasThings :> es
    => THNameToGHCName :> es
    => Eff es Type
  default coreType :: CoreTypeBuiltin a => Eff es Type
  coreType = pure $ coreTypeBuiltin @a

-- | Any marker whose type is builtin to GHC Core and thus does not require
-- a lookup to be resolved.
class CoreType a => CoreTypeBuiltin a where
  coreTypeBuiltin :: Type

-- | How to convert to and from interpretations of an 'Expr'.
--
-- Instead of directly having the interpreted representation in the typeclass
-- slot, we keep it as a type family. This is because the relation is
-- surjective: multiple expressions may have the same interpretation. As such,
-- we generally use a sort of marker value as the implementor of this function.
class CoreType a => Reify a where
  type InterpRep (es :: [Kind.Type]) a

  -- TODO: For now, just having the generic () !> es error suffices. Ideally
  -- though, we have a type family that spells out which errors may occur during
  -- either reification or intepretation. Perhaps we even need a type family for
  -- each, though I would rather not go there... In any case, I cannot write a
  -- type family of ReifyError a :: [Kind.Type] here, as Haskell type families
  -- are too slow to have a type family for (!>>). I would need to write
  -- ReifyError a es :: Kind.Constraint, which I think it much worse. With that
  -- one, I'm also still a little bit worried about compile times... I guess we
  -- could alternatively have a single error type that existentially wraps any
  -- error we might want to give. It could be a stop-gap solution...
  reify
    :: HasCallStack
    => () !> es
    => Type
    -> Eval es (InterpRep es a)
    -> Eval es (Expr es)

  interpret
    :: HasCallStack
    => () !> es
    => Type
    -> Eval es (Expr es)
    -> Eval es (InterpRep es a)

type ReifyBuiltin a = (CoreTypeBuiltin a, Reify a)

builtinReify
  :: forall a es
   . () !> es
  => ReifyBuiltin a
  => Eval es (InterpRep es a)
  -> Eval es (Expr es)
builtinReify expr = do
  let ty = coreTypeBuiltin @a
  reify @a ty expr

builtinInterpret
  :: forall a es
   . () !> es
  => ReifyBuiltin a
  => Eval es (Expr es)
  -> Eval es (InterpRep es a)
builtinInterpret expr = do
  let ty = coreTypeBuiltin @a
  interpret @a ty expr

-- | Reify marker for type variables.
--
-- The natural number is the type variable name. The other parameter defines its
-- 'Kind' via its 'CoreType'.
data RTyVar (n :: Nat) k

-- | Helper to create a type for RTyVar.
mkRTyVarTy
  :: forall n
   . KnownNat n
  => Kind
  -> Type
mkRTyVarTy kind = do
  -- SAFETY: This list is infinite.
  let idx = natVal @n Proxy
  let tv = alphaTyVars !! fromIntegral idx

  let tv' = setTyVarKind tv kind
  mkTyVarTy tv'

instance (KnownNat n, CoreType k) => CoreType (RTyVar n k) where
  coreType = do
    kind <- coreType @k
    pure $ mkRTyVarTy @n kind

instance (KnownNat n, CoreTypeBuiltin k) => CoreTypeBuiltin (RTyVar n k) where
  coreTypeBuiltin = mkRTyVarTy @n $ coreTypeBuiltin @k

instance (KnownNat n, CoreType k) => Reify (RTyVar n k) where
  type InterpRep es (RTyVar n k) = Expr es

  reify ty expr = do
    expr' <- expr
    ty' <- liftR $ exprType expr'

    -- Ensure the expression has the correct type.
    unless (eqType ty ty') do
      throwE ()

    pure expr'

  interpret ty expr = do
    expr' <- expr
    ty' <- liftR $ exprType expr'

    -- Ensure the expression has the correct type.
    unless (eqType ty ty') do
      throwE ()

    pure expr'

-- | Forall arrow reify marker.
data a +> b
infixr +>

-- | Helper function to create the type of the forall reify marker.
mkKForAllTy :: Type -> Type -> Type
mkKForAllTy argTy bodyTy = do
  let bndr = Bndr (getTyVar argTy) Specified
  mkForAllTy bndr bodyTy

instance (KnownNat n, CoreType k, CoreType b) => CoreType (RTyVar n k +> b) where
  coreType = do
    argTy <- coreType @(RTyVar n k)
    bodyTy <- coreType @b
    pure $ mkKForAllTy argTy bodyTy

instance
  ( KnownNat n
  , CoreTypeBuiltin k
  , CoreTypeBuiltin b
  ) => CoreTypeBuiltin (RTyVar n k +> b) where
  coreTypeBuiltin = do
    let argTy = coreTypeBuiltin @(RTyVar n k)
    let bodyTy = coreTypeBuiltin @b
    mkKForAllTy argTy bodyTy

instance (KnownNat n, CoreType k, Reify b) => Reify (RTyVar n k +> b) where
  type InterpRep es (RTyVar n k +> b) = Type -> Eval es (InterpRep es b)

  reify ty fun = do
    (tvar, tbody) <- failWithE () $ splitForAllTyCoVar_maybe ty
    pure $ mkLam ty \arg -> do
      -- Get the type of the body.
      subst <- liftR $ extendSubst mkEmptySubst tvar arg
      let tbody' = substTy subst tbody

      -- Compute the actual function.
      fun' <- fun
      arg' <- liftR $ forceTy arg

      reify @b tbody' $ fun' arg'

  interpret ty fun = do
    (tvar, tbody) <- failWithE () $ splitForAllCoVar_maybe ty
    pure \arg -> do
      -- Compute the actual function.
      fun' <- fun
      let arg' = pure $ mkType arg

      -- Get the type of the body.
      subst <- liftR $ extendSubst mkEmptySubst tvar arg'
      let tbody' = substTy subst tbody

      interpret @b tbody' $ mkApp fun' arg'

-- | Function arrow reify marker.
data a ~> b
infixr ~>

instance (CoreType a, CoreType b) => CoreType (a ~> b) where
  coreType = do
    argTy <- coreType @a
    resTy <- coreType @b
    pure $ mkFunTy GHC.FTF_T_T GHC.ManyTy argTy resTy

instance (CoreTypeBuiltin a, CoreTypeBuiltin b) => CoreTypeBuiltin (a ~> b) where
  coreTypeBuiltin = do
    let argTy = coreTypeBuiltin @a
    let resTy = coreTypeBuiltin @b
    mkFunTy GHC.FTF_T_T GHC.ManyTy argTy resTy

instance (Reify a, Reify b) => Reify (a ~> b) where
  type InterpRep es (a ~> b) = Eval es (InterpRep es a) -> Eval es (InterpRep es b)

  reify ty fun = do
    (_flag, _mult, argTy, resTy) <- failWithE () $ splitFunTy_maybe ty
    pure $ mkLam ty \arg -> do
      fun' <- fun
      let arg' = interpret @a argTy arg
      reify @b resTy $ fun' arg'

  interpret ty fun = do
    (_flag, _mult, argTy, resTy) <- failWithE () $ splitFunTy_maybe ty
    pure \arg -> do
      fun' <- fun
      let arg' = reify @a argTy arg
      interpret @b resTy $ mkApp fun' arg'

-- | Sized integer primitive reify marker.
--
-- Note that this is not restricted to just machine words (i.e. it can be any
-- size).
-- TODO: It is not clear that this is a Pantomime primitive... Perhaps change
-- the name a bit? 'RPIntN' maybe works (similar to how the Haskell version is
-- 'RHIntN'). Idk, it's mostly an issue for other types e.g. Integer and the
-- Pantomime symbolic Integer primitive.
data RIntN n

instance CoreType n => CoreType (RIntN n) where
  coreType = do
    name <- thNameToGhcName ''Primitive.IntN
    tc <- lookupTyCon name
    size <- coreType @n
    pure $ mkTyConApp tc [size]

instance CoreType n => Reify (RIntN n) where
  type InterpRep es (RIntN n) = SomeBV (IntN S)

  reify ty value = do
    SomeBV value' <- value
    pure $ mkLit (mkIntN value' ty)

  interpret ty value = value >>= \case
    Lit (Int value' ty') | eqType ty ty' -> pure $ SomeBV value'
    _ -> throwE ()

-- | KnownNat constraint reify marker.
data RKnownNat n

instance CoreType n => CoreType (RKnownNat n) where
  coreType = do
    name <- thNameToGhcName ''KnownNat
    tc <- lookupTyCon name
    size <- coreType @n
    pure $ mkTyConApp tc [size]

instance CoreType n => Reify (RKnownNat n) where
  type InterpRep es (RKnownNat n) = InterpRep es RNatural

  reify ty value = do
    (tc, targs) <- failWithE () $ splitTyConApp_maybe ty
    (ty', co) <- failWithE () $ instNewTyCon_maybe tc targs
    inner <- reify @RNatural ty' value
    mkCast inner $ mkSymCo co

  interpret ty value = do
    -- Unwrap the KnownNat typeclass (which is a cast over a Natural).
    (tyL, body) <- value >>= \case
      Cast body co
        | Pair tyL tyR <- coercionKind co
        , eqType ty tyR -> pure (tyL, liftUnion body)
      _ -> throwE ()

    interpret @RNatural tyL body

-- | Natural reify marker.
data RNatural

instance CoreType RNatural

instance CoreTypeBuiltin RNatural where
  coreTypeBuiltin = naturalTy

instance Reify RNatural where
  type InterpRep es RNatural = Either (SomeBV (WordN S)) ()

  reify ty expr = do
    -- Though not strictly necessary, we ensure we have the correct type.
    unless (eqType ty naturalTy) do
      throwE ()

    expr >>= \case
      Left (SomeBV value) -> do
        -- FIXME: Give proper platform size
        let dc = mkLit $ mkDataCon @64 naturalNSDataCon
        let arg = pure $ mkLit (mkWordN value wordPrimTy)
        mkApp dc arg

      Right _value -> do
        -- let _dc = mkLit $ mkDataCon @64 naturalNBDataCon
        -- let arg = pure $ mkLit (mkByteArray value byteArrayPrimTy)
        -- mkApp dc arg
        -- FIXME: Implement this once we have byte array primitives.
        undefined

  interpret ty expr = do
    -- Though not strictly necessary, we ensure we have the correct type.
    unless (eqType ty naturalTy) do
      throwE ()

    -- Gather the arguments.
    (spine, args) <- collectArgs <$> expr

    -- Check whether the spine is indeed a natural datacon.
    dc <- case spine of
      Lit (DataCon tag tc)
        | tc == naturalTyCon 
        , Just dc <- concreteDataCon tag tc -> pure dc
      _ -> throwE ()

    -- All natural DataCon have only one argument exactly. Note that we also
    -- force it here already.
    arg <- case args of
      [arg] -> arg
      _ -> throwE ()

    if
      | dc == naturalNSDataCon
      , Lit (Word value ty') <- arg
      -- TODO: We could consider turning the Int into a ByteArray, such that we
      -- have a uniform way of interpreting a Natural. I guess this would reduce
      -- the number of permitted operations though, so perhaps it's not worth
      -- it...
      , eqType ty' wordPrimTy -> pure $ Left (SomeBV value)

      | dc == naturalNBDataCon
      -- FIXME: We should have a ByteArray primitive to match on here!
      , Lit _ <- arg -> pure $ Right ()

      | otherwise -> throwE ()

-- | Integer reify marker.
data RInteger

instance CoreType RInteger

instance CoreTypeBuiltin RInteger where
  coreTypeBuiltin = integerTy

instance Reify RInteger where
  type InterpRep es RInteger = Either (SomeBV (IntN S)) ()

  reify ty expr = do
    -- Though not strictly necessary, we ensure we have the correct type.
    unless (eqType ty integerTy) do
      throwE ()

    expr >>= \case
      Left (SomeBV value) -> do
        -- FIXME: Give proper platform size
        let dc = mkLit $ mkDataCon @64 integerISDataCon
        let arg = pure $ mkLit (mkIntN value intPrimTy)
        mkApp dc arg
      Right _value -> do
        -- let _dc = mkLit $ mkDataCon @64 naturalNBDataCon
        -- let arg = pure $ mkLit (mkByteArray value byteArrayPrimTy)
        -- mkApp dc arg
        -- FIXME: Implement this once we have byte array primitives.
        undefined

  interpret ty expr = do
    -- Though not strictly necessary, we ensure we have the correct type.
    unless (eqType ty integerTy) do
      throwE ()

    -- Gather the arguments.
    (spine, args) <- collectArgs <$> expr

    -- Check whether the spine is indeed a natural datacon.
    dc <- case spine of
      Lit (DataCon tag tc)
        | tc == integerTyCon
        , Just dc <- concreteDataCon tag tc -> pure dc
      _ -> throwE ()

    -- All natural DataCon have only one argument exactly. Note that we also
    -- force it here already.
    arg <- case args of
      [arg] -> arg
      _ -> throwE ()

    if
      | dc == integerISDataCon
      , Lit (Int value ty') <- arg
      -- TODO: We could consider turning the Int into a ByteArray, such that we
      -- have a uniform way of interpreting a Integer.
      , eqType ty' intPrimTy -> pure $ Left (SomeBV value)

      | dc == integerIPDataCon
      -- FIXME: We should have a ByteArray primitive to match on here!
      , Lit _ <- arg -> pure $ Right ()

      | dc == integerINDataCon
      -- FIXME: We should have a ByteArray primitive to match on here!
      , Lit _ <- arg -> pure $ Right ()

      | otherwise -> throwE ()

-- | Boolean reify marker.
data RBool

instance CoreType RBool

instance CoreTypeBuiltin RBool where
  coreTypeBuiltin = boolTy

instance Reify RBool where
  type InterpRep _ RBool = SymBool

  reify ty expr = do
    -- Though not strictly necessary, we ensure we have the correct type.
    unless (eqType ty boolTy) do
      throwE ()

    -- Convert the symbolic boolean into a tag.
    value <- expr
    let tag = sizedBVResizeZ @_ @1 $ bitCast value

    -- FIXME: Provide proper tag size.
    mkEnumCon @64 tag boolTy

  interpret ty expr = do
    -- Though not strictly necessary, we ensure we have the correct type.
    unless (eqType ty boolTy) do
      throwE ()

    -- Convert the expression into a SymBool, if possible.
    expr >>= exprToBool

-- | Reify marker for Haskell sized integer primitives.
data RHIntN (n :: Nat)

instance
  ( KnownNat n
  , (n == 8 || n == 16 || n == 32 || n == 64) ~ True
  ) => CoreType (RHIntN n) where

instance
  ( KnownNat n
  , (n == 8 || n == 16 || n == 32 || n == 64) ~ True
  ) => CoreTypeBuiltin (RHIntN n) where
  coreTypeBuiltin = case natVal @n Proxy of
    8 -> int8PrimTy
    16 -> int16PrimTy
    32 -> int32PrimTy
    64 -> int64PrimTy
    _ -> error "unreachable due to typeclass constraint"

instance
  ( KnownNat n
  , (n == 8 || n == 16 || n == 32 || n == 64) ~ True
  ) => Reify (RHIntN n) where
  type InterpRep es (RHIntN n) = IntN S n

  reify ty value = do
    -- Though not strictly necessary, we ensure we have the correct type.
    unless (eqType ty $ coreTypeBuiltin @(RHIntN n)) do
      throwE ()

    value' <- value
    pure $ mkLit (mkIntN value' ty)

  interpret ty value = value >>= \case
    Lit (Int @m value' ty')
      | Just Refl <- eqT @n @m
      , eqType ty ty' -> pure value'
    _ -> throwE ()

-- | Reify marker for the Haskell platform sized integer primitives.
data RHIntPW (n :: Nat)

instance CoreType (RHIntPW n)

instance CoreTypeBuiltin (RHIntPW n) where
  coreTypeBuiltin = intPrimTy

instance KnownNat n => Reify (RHIntPW n) where
  type InterpRep es (RHIntPW n) = IntN S n

  reify ty value = do
    -- Though not strictly necessary, we ensure we have the correct type.
    unless (eqType ty $ coreTypeBuiltin @(RHIntPW n)) do
      throwE ()

    value' <- value
    pure $ mkLit (mkIntN value' ty)

  interpret ty value = value >>= \case
    Lit (Int @m value' ty')
      | Just Refl <- eqT @n @m
      , eqType ty ty' -> pure value'
    _ -> throwE ()

-- | Reify marker for Haskell sized integer primitives.
data RHWordN (n :: Nat)

instance
  ( KnownNat n
  , (n == 8 || n == 16 || n == 32 || n == 64) ~ True
  ) => CoreType (RHWordN n) where

instance
  ( KnownNat n
  , (n == 8 || n == 16 || n == 32 || n == 64) ~ True
  ) => CoreTypeBuiltin (RHWordN n) where

  coreTypeBuiltin = case natVal @n Proxy of
    8 -> word8PrimTy
    16 -> word16PrimTy
    32 -> word32PrimTy
    64 -> word64PrimTy
    _ -> error "unreachable due to typeclass constraint"

instance
  ( KnownNat n
  , (n == 8 || n == 16 || n == 32 || n == 64) ~ True
  ) => Reify (RHWordN n) where
  type InterpRep es (RHWordN n) = WordN S n

  reify ty value = do
    -- Though not strictly necessary, we ensure we have the correct type.
    unless (eqType ty $ coreTypeBuiltin @(RHWordN n)) do
      throwE ()

    value' <- value
    pure $ mkLit (mkWordN value' ty)

  interpret ty value = value >>= \case
    Lit (Word @m value' ty')
      | Just Refl <- eqT @n @m
      , eqType ty ty' -> pure value'
    _ -> throwE ()

-- | Reify marker for the Haskell platform sized integer primitives.
data RHWordPW (n :: Nat)

instance CoreType (RHWordPW n)

instance CoreTypeBuiltin (RHWordPW n) where
  coreTypeBuiltin = wordPrimTy

instance KnownNat n => Reify (RHWordPW n) where
  type InterpRep es (RHWordPW n) = WordN S n

  reify ty value = do
    -- Though not strictly necessary, we ensure we have the correct type.
    unless (eqType ty $ coreTypeBuiltin @(RHWordPW n)) do
      throwE ()

    value' <- value
    pure $ mkLit (mkWordN value' ty)

  interpret ty value = value >>= \case
    Lit (Word @m value' ty')
      | Just Refl <- eqT @n @m
      , eqType ty ty' -> pure value'
    _ -> throwE ()

-- | Alias for the most common kinded type variables.
type RTyVar_ n = RTyVar n RTypeKind

-- | Reify marker with kind 'Type'. I.e. the kind of lifted types.
data RTypeKind

instance CoreType RTypeKind

instance CoreTypeBuiltin RTypeKind where
  coreTypeBuiltin = liftedTypeKind

-- | Reify marker with kind 'TYPE (BoxedRep l)'.
data RBoxedRep l

-- | Helper to create a type for RBoxedRep.
mkRBoxedRepTy :: LevityType -> Type
mkRBoxedRepTy levity = do
  let rep = mkTyConApp boxedRepDataConTyCon [levity]
  mkTyConApp tYPETyCon [rep]

instance CoreType l => CoreType (RBoxedRep l) where
  coreType = do
    levity <- coreType @l
    pure $ mkRBoxedRepTy levity

instance CoreTypeBuiltin l => CoreTypeBuiltin (RBoxedRep l) where
  coreTypeBuiltin = mkRBoxedRepTy $ coreTypeBuiltin @l

-- | Reify marker with kind 'Levity'
data RLevity

instance CoreType RLevity

instance CoreTypeBuiltin RLevity where
  coreTypeBuiltin = levityTy

liftF1'
  :: Applicative f
  => (a -> b)
  -> f (f a -> f b)
liftF1' = pure . fmap

liftF2
  :: Applicative f
  => (a -> b -> c)
  -> f (a -> f (b -> c))
liftF2 f = pure $ pure . f

liftF2'
  :: Applicative f
  => (a -> b -> c)
  -> f (f a -> f (f b -> f c))
liftF2' = liftF2 . liftA2

liftF3
  :: Applicative f
  => (a -> b -> c -> d)
  -> f (a -> f (b -> f (c -> d)))
liftF3 f = pure $ liftF2 . f

liftF3'
  :: Applicative f
  => (a -> b -> c -> d)
  -> f (f a -> f (f b -> f (f c -> f d)))
liftF3' = liftF3 . liftA3

liftA4
  :: Applicative f
  => (a -> b -> c -> d -> e)
  -> (f a -> f b -> f c -> f d -> f e)
liftA4 f a b c d = f <$> a <*> b <*> c <*> d

liftF4
  :: Applicative f
  => (a -> b -> c -> d -> e)
  -> f (a -> f (b -> f (c -> f (d -> e))))
liftF4 f = pure $ liftF3 . f

liftF4'
  :: Applicative f
  => (a -> b -> c -> d -> e)
  -> f (f a -> f (f b -> f (f c -> f (f d -> f e))))
liftF4' = liftF4 . liftA4
