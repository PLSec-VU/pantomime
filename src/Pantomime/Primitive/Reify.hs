-- TODO: Write a note on why we use marker types instead of the real one.
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE PatternSynonyms #-}

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
  , RTYPE
  , RRuntimeRep
  , RTypeKind
  , RBoxedRep
  , RLevity

  -- | Type natural families and literals.
  , RTyNat
  , RAdd
  , RSub
  , RLEq

  -- | Pantomime primitives.
  , RBitVec
  , RBool
  -- , RArray

  -- -- | Haskell primitives.
  -- , RHIntN
  -- , RHIntPW
  -- , RHWordN
  -- , RHWordPW

  -- | Common Haskell types.
  -- , RKnownNat
  -- , RNatural
  -- , RInteger
  -- , RBool
  -- , RInt
  , RUnsafeEquality

  -- | Lifting function for ease of use.
  , liftF1'
  , liftF2
  , liftF2'
  , liftF3
  , liftF3'
  , liftF4
  , liftF4'
  , liftF5
  , liftF5'
  , liftF6
  , liftF6'
  , liftF7
  , liftF7'
  , liftF8
  , liftF8'
  ) where

import Pantomime.Expr
  ( Type
  , Expr (..)
  , Eval
  , EvalExpr
  , mkLam
  , mkType
  , mkApp
  , mkCon
  , mkLit
  , mkDataCon
  , mkCast
  , mkApps
  , mkCoercion
  , collectArgs
  , forceTy
  , forceCo
  , exprType
  , throwE
  , failWithE
  , liftEff
  )
import Pantomime.Subst
  ( extendSubst
  , substTy
  , mkEmptySubst
  )
-- import Pantomime.Primitive.Array qualified as Primitive
import Pantomime.Primitive.BitVector qualified as Primitive
-- import Pantomime.Grisette.BitVector (IntN, WordN)
import Pantomime.Primitive.Bool qualified as Primitive
import Pantomime.Literal (Literal (..), BuiltInTyCon)
import Pantomime.Util (SymBitVec, SomeBitVec (..))

import GHC.TypeNats (type (<=), KnownNat, Nat, natVal)
import GHC.Builtin.Types.Literals (typeNatAddTyCon, typeNatSubTyCon)
import GHC.Builtin.Types.Prim (alphaTyVars)
import GHC.Core.TyCo.Rep (LevityType)
import GHC.Core.FamInstEnv (normaliseType)
import GHC.Core.Reduction (Reduction(..))
import GHC.Core.TyCo.Compare (eqType)
import GHC.Plugins
  ( Name
  , Kind
  , ForAllTyFlag (..)
  , VarBndr (..)
  , CoercionN
  , Role (..)
  , FunTyFlag (..)
  , mkTyConTy
  , mkTyConApp
  , mkSymCo
  , mkFunTy
  , mkTyVarTy
  , mkForAllTy
  , mkNumLitTy
  , setTyVarKind
  , splitForAllCoVar_maybe
  , splitFunTy_maybe
  , splitTyConApp_maybe
  , tyConDataCons_maybe
  , coercionLKind
  , coercionRKind
  , coercionRole
  , tYPETyCon
  , levityTy
  , runtimeRepTy
  , boxedRepDataConTyCon
  , splitForAllTyCoVar_maybe
  , liftedTypeKind
  , getTyVar
  , typeKind
  , pattern ManyTy
  )

import Language.Haskell.TH qualified as TH

import Data.Proxy (Proxy(..))

import Control.Applicative (liftA3)
import Control.Monad (unless)

import Unsafe.Coerce (UnsafeEquality)

import Grisette (SymBool)

import Effectful
import Effectful.Error.Static
import Effectful.GHC.TyThing
import Effectful.GHC.TH
import Effectful.GHC.External
import Effectful.Context

-- TODO: We should move this from CoreType to BuiltinType perhaps. That is, we
-- are completely moving away from the reify working for GHC types. We only want
-- to support our own types, without caring about any interfacing. This should
-- be used only to implement primitives. This being said, we will change the
-- effect stack to only allow lookups for Pantomime primitive types.
--
-- Then there can be a simple module that connects all primitive operations to
-- their API version.
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
  type InterpRep (es :: [Effect]) a

  -- TODO: 'reify' is not a good word for this no? The Expr is more abstract
  -- than the representation...
  reify
    :: HasCallStack
    => Error () :> es
    => HasFamInstEnvs :> es
    => Context Reader BuiltInTyCon :> es
    => Type
    -> Eval es (InterpRep es a)
    -> Eval es (Expr es)

  interpret
    :: HasCallStack
    => Error () :> es
    => HasFamInstEnvs :> es
    => Context Reader BuiltInTyCon :> es
    => Type
    -> Eval es (Expr es)
    -> Eval es (InterpRep es a)

type ReifyBuiltin a = (CoreTypeBuiltin a, Reify a)

builtinReify
  :: forall a es
   . Error () :> es
  => ReifyBuiltin a
  => HasFamInstEnvs :> es
  => Context Reader BuiltInTyCon :> es
  => Eval es (InterpRep es a)
  -> Eval es (Expr es)
builtinReify expr = do
  let ty = coreTypeBuiltin @a
  reify @a ty expr

builtinInterpret
  :: forall a es
   . Error () :> es
  => ReifyBuiltin a
  => HasFamInstEnvs :> es
  => Context Reader BuiltInTyCon :> es
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
  -- TODO: This probably is not the best way to define the name (in case
  -- someone tries a very large number, this will be incredibly slow...)
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
    ty' <- liftEff $ exprType expr'

    -- Ensure the expression has the correct type.
    unless (eqType ty ty') do
      throwE ()

    pure expr'

  interpret ty expr = do
    expr' <- expr
    ty' <- liftEff $ exprType expr'

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
      subst <- liftEff $ extendSubst mkEmptySubst tvar arg
      let tbody' = substTy subst tbody

      -- Compute the actual function.
      fun' <- fun
      arg' <- liftEff $ forceTy arg

      reify @b tbody' $ fun' arg'

  interpret ty fun = do
    (tvar, tbody) <- failWithE () $ splitForAllCoVar_maybe ty
    pure \arg -> do
      -- Compute the actual function.
      fun' <- fun
      let arg' = pure $ mkType arg

      -- Get the type of the body.
      subst <- liftEff $ extendSubst mkEmptySubst tvar arg'
      let tbody' = substTy subst tbody

      interpret @b tbody' $ mkApp fun' arg'

-- | Function arrow reify marker.
data a ~> b
infixr ~>

instance (CoreType a, CoreType b) => CoreType (a ~> b) where
  coreType = do
    argTy <- coreType @a
    resTy <- coreType @b
    pure $ mkFunTy FTF_T_T ManyTy argTy resTy

instance (CoreTypeBuiltin a, CoreTypeBuiltin b) => CoreTypeBuiltin (a ~> b) where
  coreTypeBuiltin = do
    let argTy = coreTypeBuiltin @a
    let resTy = coreTypeBuiltin @b
    mkFunTy FTF_T_T ManyTy argTy resTy

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

-- | Bit vector primitive reify marker.
--
-- Note that this is not restricted to just machine words (i.e. it can be any
-- size).
data RBitVec n

instance CoreType n => CoreType (RBitVec n) where
  coreType = do
    name <- thNameToGhcName ''Primitive.BitVector
    tc <- lookupTyCon name
    size <- coreType @n
    pure $ mkTyConApp tc [size]

instance CoreType n => Reify (RBitVec n) where
  type InterpRep es (RBitVec n) = SomeBitVec SymBitVec

  reify ty value = do
    SomeBitVec value' <- value
    let lit = BitVec value'
    embedLiteral lit ty

  interpret ty expr = do
    expr' <- expr
    lit <- reifyLiteral expr' ty
    case lit of
      BitVec value' -> pure $ SomeBitVec value'
      _ -> throwE ()

data RBool

instance CoreType RBool where
  coreType = do
    name <- thNameToGhcName ''Primitive.Bool
    tc <- lookupTyCon name
    pure $ mkTyConTy tc

instance Reify RBool where
  type InterpRep es RBool = SymBool

  reify ty value = do
    value' <- value
    let lit = Bool value'
    embedLiteral lit ty

  interpret ty expr = do
    expr' <- expr
    lit <- reifyLiteral expr' ty
    case lit of
      Bool value' -> pure value'
      _ -> throwE ()

-- data RArray k v

-- instance (CoreType k, CoreType v) => CoreType (RArray k v) where
--   coreType = do
--     name <- thNameToGhcName ''Primitive.Array
--     tc <- lookupTyCon name
--     keyTy <- coreType @k
--     valTy <- coreType @v
--     pure $ mkTyConApp tc [keyTy, valTy]

-- instance (CoreType k, CoreType v) => Reify (RArray k v) where
--   type InterpRep es (RArray k v) = SomeSymArray

--   reify ty value = do
--     SomeSymArray value' <- value
--     pure $ mkLit (mkArray value' ty)

--   interpret ty expr = do
--     expr' <- expr
--     case expr' of
--       Lit (Array value ty') | eqType ty ty' -> pure $ SomeSymArray value
--       _ -> throwE ()

embedLiteral
  :: HasCallStack
  => Error () :> es
  => HasFamInstEnvs :> es
  => Context Reader BuiltInTyCon :> es
  => Literal
  -> Type
  -> EvalExpr es
embedLiteral lit ty = do
  -- Reduction for type-level naturals.
  fam <- liftEff getFamInstEnvs
  let reduction = normaliseType fam Representational ty

  -- Apply the reduction coercion.
  let lit' = mkLit lit
  let co = mkSymCo $ reductionCoercion reduction
  mkCast lit' co

-- | Literals might have nominal coercions which make them match the given type.
--
-- Instead of discarding a cast on a literal, we nominally normalise the given
-- type and apply this coercion. These coercions should cancel each other out,
-- which should return the final literal without any cast.
reifyLiteral
  :: HasCallStack
  => Error () :> es
  => HasFamInstEnvs :> es
  => Context Reader BuiltInTyCon :> es
  => Expr es
  -> Type
  -> Eval es Literal
reifyLiteral expr ty = do
  fam <- liftEff getFamInstEnvs
  let reduction = normaliseType fam Representational ty

  -- Apply the reduction coercion.
  let co = reductionCoercion reduction
  expr' <- mkCast expr co
  case expr' of
    Lit lit -> pure lit
    _ -> throwE ()

data RUnsafeEquality k a b

instance (CoreType k, CoreType a, CoreType b) => CoreType (RUnsafeEquality k a b) where
  coreType = do
    kind <- coreType @k
    tyL <- coreType @a
    tyR <- coreType @b

    name <- thNameToGhcName ''UnsafeEquality
    tc <- lookupTyCon name
    pure $ mkTyConApp tc [kind, tyL, tyR]

instance (CoreType k, CoreType a, CoreType b) => Reify (RUnsafeEquality k a b) where
  type InterpRep es (RUnsafeEquality k a b) = CoercionN

  reify ty co = do
    (tc, args) <- failWithE () $ splitTyConApp_maybe ty

    -- Fetch the 'UnsafeRefl' DataCon.
    dc <- case tyConDataCons_maybe tc of
      Just [dc] -> pure dc
      _ -> throwE ()

    -- Fetch the type arguments directly.
    (kind, tyL, tyR) <- case args of
      [kind, tyL, tyR] -> pure (kind, tyL, tyR)
      _ -> throwE ()

    -- Get the spine of this expression.
    let spine = mkCon $ mkDataCon @64 dc

    -- Force the coercion.
    co' <- co

    -- Check whether the coercion matches the expected type.
    let coerces = and
          [ eqType tyL $ coercionRKind co'
          , eqType tyR $ coercionLKind co'
          , coercionRole co' == Nominal
          ]
    unless coerces do
      throwE ()

    -- Return the final expression.
    mkApps spine $ pure <$> [mkType kind, mkType tyL, mkType tyR, mkCoercion co']

  interpret ty expr = do
    expr' <- expr
    ty' <- liftEff $ exprType expr'

    -- Ensure the expression has the correct type.
    unless (eqType ty ty') do
      throwE ()

    -- Gather just the coercion argument.
    let (_spine, args) = collectArgs expr'
    case args of
      [_kind, _ty, co] -> liftEff $ forceCo co
      _ -> throwE ()

-- | Alias for the most common kinded type variables.
type RTyVar_ n = RTyVar n RTypeKind

-- | Reify marker for 'TYPE'.
data RTYPE r

instance CoreType r => CoreType (RTYPE r) where
  coreType = do
    rep <- coreType @r
    pure $ mkTyConApp tYPETyCon [rep]

instance CoreTypeBuiltin r => CoreTypeBuiltin (RTYPE r) where
  coreTypeBuiltin = do
    let rep = coreTypeBuiltin @r
    mkTyConApp tYPETyCon [rep]

-- | Reify marker for 'RuntimeRep'.
data RRuntimeRep

instance CoreType RRuntimeRep

instance CoreTypeBuiltin RRuntimeRep where
  coreTypeBuiltin = runtimeRepTy

-- | Reify marker with kind 'Type'. I.e. the kind of lifted types.
data RTypeKind

instance CoreType RTypeKind

instance CoreTypeBuiltin RTypeKind where
  coreTypeBuiltin = liftedTypeKind

-- TODO: I guess this name is not great. RBoxedRep should just be the inner
-- thing. We could then make a type alias using RTYPE.
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

-- | Reify marker for type-naturals.
data RTyNat (n :: Nat)

instance KnownNat n => CoreType (RTyNat n) where

instance KnownNat n => CoreTypeBuiltin (RTyNat n) where
  coreTypeBuiltin = do
    let value = natVal @n Proxy
    mkNumLitTy $ toInteger value

-- | Reify marker for adding two type-level naturals.
data RAdd n m

instance (CoreType n, CoreType m) => CoreType (RAdd n m) where
  coreType = do
    l <- coreType @n
    r <- coreType @m
    pure $ mkTyConApp typeNatAddTyCon [l, r]

instance (CoreTypeBuiltin n, CoreTypeBuiltin m) => CoreTypeBuiltin (RAdd n m) where
  coreTypeBuiltin = do
    let l = coreTypeBuiltin @n
    let r = coreTypeBuiltin @m
    mkTyConApp typeNatAddTyCon [l, r]

-- | Reify marker for adding two type-level naturals.
data RSub n m

instance (CoreType n, CoreType m) => CoreType (RSub n m) where
  coreType = do
    l <- coreType @n
    r <- coreType @m
    pure $ mkTyConApp typeNatSubTyCon [l, r]

instance (CoreTypeBuiltin n, CoreTypeBuiltin m) => CoreTypeBuiltin (RSub n m) where
  coreTypeBuiltin = do
    let l = coreTypeBuiltin @n
    let r = coreTypeBuiltin @m
    mkTyConApp typeNatSubTyCon [l, r]

-- | Reify marker less than or equal constraint.
data RLEq n m

instance (CoreType n, CoreType m) => CoreType (RLEq n m) where
  coreType = do
    name <- thNameToGhcName ''(<=)
    tc <- lookupTyCon name
    l <- coreType @n
    r <- coreType @m
    -- TODO: Isn't there a better way to get the kind? At least one that fails
    -- slightly more gracefully?
    let kind = typeKind l
    pure $ mkTyConApp tc [kind, l, r]

instance (CoreType n, CoreType m) => Reify (RLEq n m) where
  type InterpRep es (RLEq n m) = Expr es

  -- TODO: This implementation doesn't really do anything. We should make it
  -- more accurate sometime!
  reify ty expr = do
    expr' <- expr
    ty' <- liftEff $ exprType expr'

    -- Ensure the expression has the correct type.
    unless (eqType ty ty') do
      throwE ()

    pure expr'

  interpret ty expr = do
    expr' <- expr
    ty' <- liftEff $ exprType expr'

    -- Ensure the expression has the correct type.
    unless (eqType ty ty') do
      throwE ()

    pure expr'

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

liftA5
  :: Applicative f
  => (a -> b -> c -> d -> e -> g)
  -> (f a -> f b -> f c -> f d -> f e -> f g)
liftA5 f a b c d e = f <$> a <*> b <*> c <*> d <*> e

liftF5
  :: Applicative f
  => (a -> b -> c -> d -> e -> g)
  -> f (a -> f (b -> f (c -> f (d -> f (e -> g)))))
liftF5 f = pure $ liftF4 . f

liftF5'
  :: Applicative f
  => (a -> b -> c -> d -> e -> g)
  -> f (f a -> f (f b -> f (f c -> f (f d -> f (f e -> f g)))))
liftF5' = liftF5 . liftA5

liftA6
  :: Applicative f
  => (a -> b -> c -> d -> e -> g -> h)
  -> (f a -> f b -> f c -> f d -> f e -> f g -> f h)
liftA6 f a b c d e g = f <$> a <*> b <*> c <*> d <*> e <*> g

liftF6
  :: Applicative f
  => (a -> b -> c -> d -> e -> g -> h)
  -> f (a -> f (b -> f (c -> f (d -> f (e -> f (g -> h))))))
liftF6 f = pure $ liftF5 . f

liftF6'
  :: Applicative f
  => (a -> b -> c -> d -> e -> g -> h)
  -> f (f a -> f (f b -> f (f c -> f (f d -> f (f e -> f (f g -> f h))))))
liftF6' = liftF6 . liftA6

liftA7
  :: Applicative f
  => (a -> b -> c -> d -> e -> g -> h -> i)
  -> (f a -> f b -> f c -> f d -> f e -> f g -> f h -> f i)
liftA7 f a b c d e g i = f <$> a <*> b <*> c <*> d <*> e <*> g <*> i

liftF7
  :: Applicative f
  => (a -> b -> c -> d -> e -> g -> h -> i)
  -> f (a -> f (b -> f (c -> f (d -> f (e -> f (g -> f (h -> i)))))))
liftF7 f = pure $ liftF6 . f

liftF7'
  :: Applicative f
  => (a -> b -> c -> d -> e -> g -> h -> i)
  -> f (f a -> f (f b -> f (f c -> f (f d -> f (f e -> f (f g -> f (f h -> f i)))))))
liftF7' = liftF7 . liftA7

liftA8
  :: Applicative f
  => (a -> b -> c -> d -> e -> g -> h -> i -> j)
  -> (f a -> f b -> f c -> f d -> f e -> f g -> f h -> f i -> f j)
liftA8 f a b c d e g i j = f <$> a <*> b <*> c <*> d <*> e <*> g <*> i <*> j

liftF8
  :: Applicative f
  => (a -> b -> c -> d -> e -> g -> h -> i -> j)
  -> f (a -> f (b -> f (c -> f (d -> f (e -> f (g -> f (h -> f (i -> j))))))))
liftF8 f = pure $ liftF7 . f

liftF8'
  :: Applicative f
  => (a -> b -> c -> d -> e -> g -> h -> i -> j)
  -> f (f a -> f (f b -> f (f c -> f (f d -> f (f e -> f (f g -> f (f h -> f (f i -> f j))))))))
liftF8' = liftF8 . liftA8
