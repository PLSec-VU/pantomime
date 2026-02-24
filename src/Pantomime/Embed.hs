{-# LANGUAGE PatternSynonyms #-}

module Pantomime.Embed
  ( Ty (..)
  , TypeKind
  , Binder (..)
  , SomeArray (..)
  , Repr
  , Reflect (..)
  , STy (..)
  , embed
  , embed'
  , project
  , project'

  -- | Helper functions to make embeddings more ergonomic to write.
  , liftF1
  , liftF2
  , liftF3
  , liftF4
  , liftF5
  , liftF6
  , liftF7
  , liftF8
  ) where

import Data.Char (ord, chr)
import Data.Data (Proxy (..))
import Data.Void (Void, absurd)

import Effectful
import Effectful.Error.Static (Error, HasCallStack)
import Effectful.Context
import Effectful.GHC.External (HasFamInstEnvs, getFamInstEnvs)

import GHC.Builtin.Types.Literals (typeNatAddTyCon)
import GHC.Builtin.Uniques (mkAlphaTyVarUnique)
import GHC.Core.Type (substTy)
import GHC.Core.FamInstEnv (normaliseType)
import GHC.Core.Reduction (Reduction (..))
import GHC.Core.TyCo.Rep (Type (..))
import GHC.Plugins
  ( Subst
  , FunTyFlag (..)
  , VarBndr (..)
  , ForAllTyFlag (..)
  , Kind
  , TyVar
  , CoercionN
  , Role (..)
  , mkTyConTy
  , mkTyConApp
  , mkFunTy
  , mkForAllTy
  , mkTyVar
  , mkInternalName
  , mkTyVarOcc
  , mkTyVarTy
  , mkNumLitTy
  , mkSubCo
  , mkSymCo
  , mkTransCo
  , splitTyConApp_maybe
  , tyConDataCons_maybe
  , instNewTyCon_maybe
  , noSrcSpan
  , extendTvSubst
  , naturalTy
  , tYPETyCon
  , runtimeRepTy
  , boxedRepDataConTyCon
  , liftedDataConTy
  , levityTy
  , pattern ManyTy
  )
import GHC.TypeLits
  ( Nat
  , KnownNat
  , SomeNat
  , someNatVal
  , natVal
  )

import Grisette (SymInteger, SymBool, ToCon (..))
import Grisette.Internal.SymPrim.SymArray (SymArray)

import Pantomime.Expr
  ( Expr (..)
  , Literal (..)
  , Eval
  , EvalExpr
  , mkLit
  , mkCon
  , mkDataCon
  , mkBool
  , mkInteger
  , mkBitVec
  , mkArray
  , mkLam
  , mkApp
  , mkApps
  , mkType
  , mkCoercion
  , mkCast
  , collectArgs
  , forceTy
  , forceCo
  , liftEff
  , throwE
  , failWithE, pprArg, dbgE
  )
import Pantomime.Util (SomeBitVec (..), SymBitVec)
import Pantomime.Literal
  ( BuiltInTyCon (..)
  , LiteralTypeable
  , SomeLiteralType
  , projectLitTy
  )

-- TODO: We could think about making this slightly more structured? Maybe
-- introduce a language similar to a GHC Type? Really, the only reason we are
-- not using GHC types is because we don't have all TyCon statically available
-- no? Idk, I'd have to think about this.
data Ty where
  BoolTy :: Ty
  IntegerTy :: Ty
  BitVecTy :: Ty -> Ty
  ArrayTy :: Ty -> Ty -> Ty
  PrimitiveTy :: Ty -> Ty
  (:->) :: Ty -> Ty -> Ty
  (:.) :: Binder -> Ty -> Ty
  TyVar :: Nat -> Ty -> Ty
  -- TODO: Ideally, we remove the dependency on 'Natural' from 'base'
  -- completely. We'll have to swap away from the standard KnownNat for this.
  -- This is possible, but would require a type check plugin to fill in an
  -- equivalent KnownNat that uses pantomime Integer. For now, we just magically
  -- reify the natural from the type. This way, we don't actually have to know
  -- the representation of natural. Note, the representation of natural is
  -- fragile as a user can dictate it. Hence, a dependency on this would be bad.
  NaturalTy :: Ty
  Natural :: Nat -> Ty
  (:+) :: Ty -> Ty -> Ty
  (:<=) :: Ty -> Ty -> Ty
  KnownNatTy :: Ty -> Ty
  TYPE :: Ty -> Ty
  RuntimeRepTy :: Ty
  BoxedRep :: Ty -> Ty
  LevityTy :: Ty
  Lifted :: Ty
  UnsafeEqualityTy :: Ty -> Ty -> Ty -> Ty
  -- TODO: We probably want UnsafeEqualityTy here as well! Alternatively we
  -- could expose our own version, but I don't see the point!

type TypeKind = TYPE (BoxedRep Lifted)

infixr :->
infixr :.

-- | Helper to make binder on forall read more natural.
data Binder where
  Forall :: Nat -> Ty -> Binder

-- | Helper for term level representation of array type.
data SomeArray where
  SomeArray ::
     ( LiteralTypeable k
     , LiteralTypeable v
     )
    => SymArray k v
    -> SomeArray

class Reflect ty where
  reflect :: STy ty

instance Reflect BoolTy where
  reflect = SBoolTy

instance Reflect IntegerTy where
  reflect = SIntegerTy

instance (Reflect k, Reflect v) => Reflect (ArrayTy k v) where
  reflect = SArrayTy reflect reflect

instance Reflect a => Reflect (PrimitiveTy a) where
  reflect = SPrimitiveTy reflect

instance Reflect n => Reflect (BitVecTy n) where
  reflect = SBitVecTy reflect

instance (Reflect a, Reflect b) => Reflect (a :-> b) where
  reflect = SLambda reflect reflect

instance (KnownNat n, Reflect a, Reflect b) => Reflect ('Forall n a :. b) where
  reflect = SForall reflect reflect

instance (KnownNat n, Reflect k) => Reflect ('TyVar n k) where
  reflect = STyVar reflect

instance Reflect NaturalTy where
  reflect = SNaturalTy

instance Reflect n => Reflect (KnownNatTy n) where
  reflect = SKnownNatTy reflect

instance KnownNat n => Reflect (Natural n) where
  reflect = SNatural @n

instance (Reflect l, Reflect r) => Reflect (l :+ r) where
  reflect = SAddTy reflect reflect

instance (Reflect l, Reflect r) => Reflect (l :<= r) where
  reflect = SLEqTy reflect reflect

instance Reflect r => Reflect (TYPE r) where
  reflect = STYPE reflect

instance Reflect RuntimeRepTy where
  reflect = SRuntimeRepTy

instance Reflect r => Reflect (BoxedRep r) where
  reflect = SBoxedRep reflect

instance Reflect LevityTy where
  reflect = SLevityTy

instance Reflect Lifted where
  reflect = SLifted

instance (Reflect k, Reflect a, Reflect b) => Reflect (UnsafeEqualityTy k a b) where
  reflect = SUnsafeEqualityTy reflect reflect reflect

type family Repr a es where
  Repr BoolTy _ = SymBool
  Repr IntegerTy _ = SymInteger
  Repr (BitVecTy _) _ = SomeBitVec SymBitVec
  Repr (ArrayTy _ _) _ = SomeArray
  Repr (PrimitiveTy _) _ = (CoercionN, SomeLiteralType)
  Repr (a :-> b) es = Eval es (Repr a es) -> Eval es (Repr b es)
  -- Whilst we could technically extract the 'Repr' of the forall argument, it
  -- would be very cumbersome as it is a type and not a term. Instead, we just
  -- leave it abstractly as a 'Type' for now. Note that we don't need to wrap
  -- it in 'Eval' as forcing a 'Type' should always be possible.
  Repr (_ :. b) es = Type -> Eval es (Repr b es)
  Repr ('TyVar _ _) es = Expr es
  Repr NaturalTy _ = Void
  Repr (Natural _) _ = Void
  Repr (_ :+ _) _ = Void
  Repr (_ :<= _) _ = ()
  Repr (KnownNatTy _) _ = SomeNat
  Repr (TYPE _) _ = Void
  Repr RuntimeRepTy _ = Void
  Repr (BoxedRep _) _ = Void
  Repr LevityTy _ = Void
  Repr Lifted _ = Void
  Repr (UnsafeEqualityTy _ _ _) _ = CoercionN

-- TODO: I guess having the whole type thing is a bit overkill. Really, we could
-- just remove it and place the 'Repr' typeclass inside of the rhs of 'STy'
-- here. I'll have to consider if it is worth it.
data STy a where
  SBoolTy :: STy 'BoolTy
  SIntegerTy :: STy 'IntegerTy
  SBitVecTy :: STy n -> STy ('BitVecTy n)
  SArrayTy :: STy k -> STy v -> STy ('ArrayTy k v)
  SPrimitiveTy :: STy a -> STy ('PrimitiveTy a)
  SLambda :: STy a -> STy b -> STy (a ':-> b)
  SForall :: KnownNat n => STy k -> STy b -> STy ('Forall n k ':. b)
  STyVar :: KnownNat n => STy k -> STy ('TyVar n k)
  SNaturalTy :: STy 'NaturalTy
  SNatural :: KnownNat n => STy ('Natural n)
  SAddTy :: STy l -> STy r -> STy (l ':+ r)
  SLEqTy :: STy l -> STy r -> STy (l ':<= r)
  SKnownNatTy :: STy n -> STy ('KnownNatTy n)
  STYPE :: STy r -> STy ('TYPE r)
  SRuntimeRepTy :: STy 'RuntimeRepTy
  SBoxedRep :: STy l -> STy ('BoxedRep l)
  SLevityTy :: STy 'LevityTy
  SLifted :: STy 'Lifted
  SUnsafeEqualityTy :: STy k -> STy a -> STy b -> STy ('UnsafeEqualityTy k a b)

embed
  :: forall a es
   . HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => Reflect a
  => Subst
  -> Eval es (Repr a es)
  -> EvalExpr es
embed subst repr = embed' subst (reflect @a) repr

project
  :: forall a es
   . HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => Reflect a
  => Subst
  -> EvalExpr es
  -> Eval es (Repr a es)
project subst repr = project' subst (reflect @a) repr

-- TODO: 'embed'' and 'project'' are mutually recursive and grow the callstack.
-- We should adjust it so this doesn't occur.
embed'
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => Subst
  -> STy a
  -> Eval es (Repr a es)
  -> EvalExpr es
embed' subst sty repr = case sty of
  SBoolTy -> do
    b <- repr
    pure $ mkLit (mkBool b)
  SIntegerTy -> do
    i <- repr
    pure $ mkLit (mkInteger i)
  SBitVecTy _ -> do
    SomeBitVec bv <- repr
    let lit = mkLit $ mkBitVec bv
    Reduction co _ <- liftEff $ normaliseSTy subst Nominal sty
    let co' = mkSymCo $ mkSubCo co
    mkCast lit co'
  SArrayTy _ _ -> do
    SomeArray arr <- repr
    let lit = mkLit $ mkArray arr
    Reduction co _ <- liftEff $ normaliseSTy subst Nominal sty
    let co' = mkSymCo $ mkSubCo co
    mkCast lit co'
  SPrimitiveTy _ -> throwE ()
  SLambda aty rty -> do
    -- Gather the type for the lambda.
    ty <- liftEff $ embedSTy subst sty
    pure $ mkLam ty \arg -> do
      let arg' = project' subst aty arg
      fun <- repr
      embed' subst rty $ fun arg'
  SForall @n aty rty -> do
    -- Gather the type for the lambda.
    ty <- liftEff $ embedSTy subst sty
    pure $ mkLam ty \arg -> do
      -- Gather the function and argument.
      fun <- repr
      arg' <- liftEff $ forceTy arg

      -- Extend the substition.
      tv <- liftEff $ mkTemplateTyVar' @n aty
      let subst' = extendTvSubst subst tv arg'

      -- Construct the final expression.
      embed' subst' rty $ fun arg'
  STyVar _kind -> do
    expr <- repr
    Reduction co _ <- liftEff $ normaliseSTy subst Nominal sty
    let co' = mkSymCo $ mkSubCo co
    mkCast expr co'
  SNaturalTy -> repr >>= absurd
  SNatural -> repr >>= absurd
  SAddTy _ _ -> repr >>= absurd
  SLEqTy _ _ -> throwE ()
  SKnownNatTy _n -> throwE ()
  STYPE _ -> repr >>= absurd
  SRuntimeRepTy -> repr >>= absurd
  SBoxedRep _ -> repr >>= absurd
  SLevityTy -> repr >>= absurd
  SLifted -> repr >>= absurd
  SUnsafeEqualityTy _ _ _ -> do
    -- Get the type of the expression.
    ty <- liftEff $ embedSTy subst sty
    (tc, args) <- failWithE () $ splitTyConApp_maybe ty

    -- Fetch the 'UnsafeRefl' DataCon.
    dc <- case tyConDataCons_maybe tc of
      Just [dc] -> pure dc
      _ -> throwE ()

    -- Construct the spine.
    let spine = mkCon $ mkDataCon @64 dc

    -- Fetch the type arguments directly.
    (kind, tyL, tyR) <- case args of
      [kind, tyL, tyR] -> pure (kind, tyL, tyR)
      _ -> throwE ()

    -- Force the coercion.
    co <- repr

    -- Construct the final expressionexpression
    mkApps spine $ pure <$> [mkType kind, mkType tyL, mkType tyR, mkCoercion co]

project'
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => Subst
  -> STy a
  -> EvalExpr es
  -> Eval es (Repr a es)
project' subst sty expr = case sty of
  SBoolTy -> expr >>= \case
    Lit (Bool b) -> pure b
    _ -> throwE ()
  SIntegerTy -> expr >>= \case
    Lit (Integer i) -> pure i
    _ -> throwE ()
  SBitVecTy _n -> do
    Reduction co _ <- liftEff $ normaliseSTy subst Nominal sty
    inner <- expr
    expr' <- mkCast inner $ mkSubCo co
    case expr' of
      Lit (BitVec bv) -> pure $ SomeBitVec bv
      _ -> throwE ()
  SArrayTy _ _ -> do
    Reduction co _ <- liftEff $ normaliseSTy subst Nominal sty
    inner <- expr
    expr' <- mkCast inner $ mkSubCo co
    case expr' of
      Lit (Array bv) -> pure $ SomeArray bv
      _ -> throwE ()
  SPrimitiveTy pty -> do
    _ <- expr
    pty' <- liftEff $ embedSTy subst pty
    liftEff $ projectLitTy pty'
  SLambda aty rty -> pure \arg -> do
    fun <- expr
    let arg' = embed' subst aty arg
    project' subst rty $ mkApp fun arg'
  SForall @n aty rty -> pure \arg -> do
    -- Gather the function and argument.
    fun <- expr
    let arg' = pure $ mkType arg

    -- Extend the substition.
    tv <- liftEff $ mkTemplateTyVar' @n aty
    let subst' = extendTvSubst subst tv arg

    -- Construct the final expression.
    project' subst' rty $ mkApp fun arg'
  STyVar _kind -> do
    Reduction co _ <- liftEff $ normaliseSTy subst Nominal sty
    repr <- expr
    mkCast repr $ mkSubCo co
  SNaturalTy -> throwE ()
  SNatural -> throwE ()
  SAddTy _ _ -> throwE ()
  SLEqTy _ _ -> do
    -- TODO: I guess we should actually ensure that this is well formed? It's
    -- a type family though, so I'm not sure how much actually remains of this
    -- thing. Same for other type families in here btw (like 'Primitive').
    _ <- expr
    pure ()
  SKnownNatTy _ -> do
    ty <- liftEff $ embedSTy subst sty

    -- Construct a coercion from the Pantomime 'KnownNat' to 'Integer'. Note
    -- that we do not want to fully instantiate newtypes as this would lead us
    -- to the Haskell 'Integer'.
    co <- failWithE () do
      (tc, args) <- splitTyConApp_maybe ty
      (ty', co) <- instNewTyCon_maybe tc args
      (tc', args') <- splitTyConApp_maybe ty'
      (_, co') <- instNewTyCon_maybe tc' args'
      pure $ mkTransCo co co'

    let expr' = expr >>= flip mkCast co

    expr' >>= \case
      -- TODO: It would probably be good to distinguish between two errors here.
      -- If we just don't have an integer value, then we actually should
      -- error. If we do have one, but we could just not reduce it to a concrete
      -- value, the error should be something closed to an 'unknown' SMT solver
      -- result. Nothing in fact is invalid, it is just not solvable.
      Lit (Integer i) | Just n <- toCon i >>= someNatVal -> pure n
      _ -> throwE ()
  STYPE _ -> throwE ()
  SRuntimeRepTy -> throwE ()
  SBoxedRep _ -> throwE ()
  SLevityTy -> throwE ()
  SLifted -> throwE ()
  SUnsafeEqualityTy _ _ _ -> do
    expr' <- expr
    let (_spine, args) = collectArgs expr'
    case args of
      [_kind, _ty, co] -> liftEff $ forceCo co
      _ -> throwE ()

embedSTy
  :: HasCallStack
  => Context Reader BuiltInTyCon :> es
  => Subst
  -> STy a
  -> Eff es Type
embedSTy subst sty = do
  ty <- embedSTy' sty
  pure $ substTy subst ty

embedSTy'
  :: HasCallStack
  => Context Reader BuiltInTyCon :> es
  => STy a
  -> Eff es Type
embedSTy' ty = do
  BuiltInTyCon { .. } <- get
  case ty of
    SBoolTy -> pure $ mkTyConTy tcBool
    SIntegerTy -> pure $ mkTyConTy tcInteger
    SBitVecTy n -> do
      n' <- embedSTy' n
      pure $ mkTyConApp tcBitVec [n']
    SArrayTy kty vty -> do
      kty' <- embedSTy' kty
      vty' <- embedSTy' vty
      pure $ mkTyConApp tcArray [kty', vty']
    SPrimitiveTy pty -> do
      pty' <- embedSTy' pty
      pure $ mkTyConApp tcPrimitive [pty']
    SLambda aty rty -> do
      aty' <- embedSTy' aty
      rty' <- embedSTy' rty
      pure $ mkFunTy FTF_T_T ManyTy aty' rty'
    SForall @n aty rty -> do
      tv <- mkTemplateTyVar' @n aty
      let bndr = Bndr tv Specified
      rty' <- embedSTy' rty
      pure $ mkForAllTy bndr rty'
    STyVar @n kind -> do
      tv <- mkTemplateTyVar' @n kind
      pure $ mkTyVarTy tv
    SNaturalTy -> pure $ naturalTy
    SNatural @n -> pure $ mkNumLitTy (natVal @n Proxy)
    SAddTy l r -> do
      l' <- embedSTy' l
      r' <- embedSTy' r
      pure $ mkTyConApp typeNatAddTyCon [l', r']
    SLEqTy l r -> do
      l' <- embedSTy' l
      r' <- embedSTy' r
      pure $ mkTyConApp tcLEqNat [l', r']
    SKnownNatTy n -> do
      n' <- embedSTy' n
      pure $ mkTyConApp tcKnownNat [n']
    STYPE rep -> do
      rep' <- embedSTy' rep
      pure $ mkTyConApp tYPETyCon [rep']
    SRuntimeRepTy -> pure runtimeRepTy
    SBoxedRep levity -> do
      levity' <- embedSTy' levity
      pure $ mkTyConApp boxedRepDataConTyCon [levity']
    SLevityTy -> pure levityTy
    SLifted -> pure liftedDataConTy
    SUnsafeEqualityTy k a b -> do
      k' <- embedSTy' k
      a' <- embedSTy' a
      b' <- embedSTy' b
      pure $ mkTyConApp tcUnsafeEquality [k', a', b']

mkTemplateTyVar'
  :: forall n a es
   . HasCallStack
  => KnownNat n
  => Context Reader BuiltInTyCon :> es
  => STy a
  -> Eff es TyVar
mkTemplateTyVar' kind = do
  let n = fromInteger $ natVal @n Proxy
  -- TODO: This is mutually recursive with 'embedSTy''. We should restrict
  -- callstack growth.
  kind' <- embedSTy' kind
  pure $ mkTemplateTyVar n kind'

-- | Create a type variable that is uniquely identified by the given 'Int'.
mkTemplateTyVar
  :: Int
  -> Kind
  -> TyVar
mkTemplateTyVar idx kind = do
  let unique = mkAlphaTyVarUnique idx
  let chI = idx + ord 'a'
  let str = if
        | chI <= ord 'z' -> [chr chI]
        | otherwise -> 't' : show idx
  let occ = mkTyVarOcc str
  let name = mkInternalName unique occ noSrcSpan
  mkTyVar name kind

normaliseSTy
  :: HasCallStack
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => Subst
  -> Role
  -> STy n
  -> Eff es Reduction
normaliseSTy subst role sty = do
  ty <- embedSTy subst sty
  fam <- getFamInstEnvs
  pure $ normaliseType fam role ty

liftF1
  :: Applicative f
  => (a -> b)
  -> f (a -> b)
liftF1 = pure

liftF2
  :: Applicative f
  => (a -> b -> c)
  -> f (a -> f (b -> c))
liftF2 f = pure $ liftF1 . f

liftF3
  :: Applicative f
  => (a -> b -> c -> d)
  -> f (a -> f (b -> f (c -> d)))
liftF3 f = pure $ liftF2 . f

liftF4
  :: Applicative f
  => (a -> b -> c -> d -> e)
  -> f (a -> f (b -> f (c -> f (d -> e))))
liftF4 f = pure $ liftF3 . f

liftF5
  :: Applicative f
  => (a -> b -> c -> d -> e -> g)
  -> f (a -> f (b -> f (c -> f (d -> f (e -> g)))))
liftF5 f = pure $ liftF4 . f

liftF6
  :: Applicative f
  => (a -> b -> c -> d -> e -> g -> h)
  -> f (a -> f (b -> f (c -> f (d -> f (e -> f (g -> h))))))
liftF6 f = pure $ liftF5 . f

liftF7
  :: Applicative f
  => (a -> b -> c -> d -> e -> g -> h -> i)
  -> f (a -> f (b -> f (c -> f (d -> f (e -> f (g -> f (h -> i)))))))
liftF7 f = pure $ liftF6 . f

liftF8
  :: Applicative f
  => (a -> b -> c -> d -> e -> g -> h -> i -> j)
  -> f (a -> f (b -> f (c -> f (d -> f (e -> f (g -> f (h -> f (i -> j))))))))
liftF8 f = pure $ liftF7 . f
