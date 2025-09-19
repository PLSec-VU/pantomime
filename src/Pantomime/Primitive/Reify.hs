module Pantomime.Primitive.Reify
  -- | Reify typeclasses.
  ( Reify (..)
  , ReifyBuiltin (..)
  , builtinReify
  , Quantifier (..)

  -- | Lambdas and quantifiers.
  , type (~>)
  , type (+>)
  , AlphaNat

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

  -- | Lifting function for ease of use.
  , liftF1'
  , liftF2
  , liftF2'
  , liftF3
  , liftF3'
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
  , mkWordN
  , mkCast
  , collectArgs
  , concreteDataCon
  , throwError'
  , whyFail'
  )
import Pantomime.Subst
  ( Subst
  , extendSubst
  , substTy
  , substTyVar
  )
import Pantomime.Primitive.Operations qualified as Primitive
import Pantomime.Grisette.BitVector (IntN, WordN)
import Pantomime.Grisette.SomeBV (SomeBV (..))

import GHC.TypeNats (KnownNat, Nat, natVal)
import GHC.Builtin.Types.Prim
  ( alphaTyVar
  , wordPrimTy
  , intPrimTy
  , intPrimTyCon
  , int8PrimTyCon
  , int16PrimTyCon
  , int32PrimTyCon
  , int64PrimTyCon
  , wordPrimTyCon
  , word8PrimTyCon
  , word16PrimTyCon
  , word32PrimTyCon
  , word64PrimTyCon
  , levPolyBetaTyVar
  )
import GHC.Core.TyCo.Compare (eqType)
import GHC.Plugins qualified as GHC
import GHC.Plugins
  ( Name
  , TyCon
  , TyVar
  , ForAllTyBinder
  , ForAllTyFlag (..)
  , VarBndr (..)
  , mkTyConApp
  , mkSymCo
  , setTyVarKind
  , mkTyVarTy
  , mkForAllTy
  , binderVar
  , coercionRKind
  , instNewTyCon_maybe
  , naturalTy
  , naturalTyCon
  , naturalNSDataCon
  , naturalNBDataCon
  , integerTy
  , integerTyCon
  , integerINDataCon
  , integerISDataCon
  , integerIPDataCon
  , mkTyConTy
  , tYPETyCon
  , boxedRepDataConTyCon
  )

import Language.Haskell.TH qualified as TH

import Data.Type.Bool (type (||))
import Data.Type.Equality (type (==))
import Data.Typeable (Proxy(..), type (:~:) (..), eqT)

import Control.Applicative (liftA3)

import Grisette.Unified (EvalModeTag(..))
import Grisette (liftUnion)

import Effectful
import Effectful.Error.Static
import Effectful.GHC.TyThing
import Effectful.GHC.TH

class Reify a where
  type InterpRep a

  data TypeInfo a

  typeInfo
    :: forall es
     . HasCallStack
    => Error (LookupError TH.Name) :> es
    => Error (LookupError Name) :> es
    => HasThings :> es
    => THNameToGHCName :> es
    => Eff es (TypeInfo a)

  reifiedTy
    :: TypeInfo a
    -> Type

  reify
    :: TypeInfo a
    -> Subst
    -> Eval (InterpRep a)
    -> Eval Expr

  interpret
    :: TypeInfo a
    -- TODO: Do we really need this substitution here?
    -> Subst
    -> Eval Expr
    -> Eval (InterpRep a)

class Reify a => ReifyBuiltin a where
  builtinTypeInfo :: TypeInfo a

builtinReify
  :: forall a
   . ReifyBuiltin a
  => Subst
  -> Eval (InterpRep a)
  -> Eval Expr
builtinReify subst expr = do
  let info = builtinTypeInfo @a
  reify info subst expr

class Quantifier a where
  quantifier :: ForAllTyBinder

-- -- | Polymorphic reify marker.
-- data RPoly a

-- instance Quantifier a => Reify (RPoly a) where
--   type InterpRep (RPoly a) = Expr

--   data TypeInfo (RPoly a) = PolyInfo

--   typeInfo = pure builtinTypeInfo

--   reifiedTy _ = mkTyVarTy $ binderVar (quantifier @a)

--   reify = undefined

--   interpret = undefined

-- instance Quantifier a => ReifyBuiltin (RPoly a) where
--   builtinTypeInfo = PolyInfo

-- | Forall arrow reify marker.
data a +> b
infixr +>

instance (Quantifier a, Reify b) => Reify (a +> b) where
  type InterpRep (a +> b) = InterpRep b

  data TypeInfo (a +> b) = ForAllInfo
    { quantInfo :: ForAllTyBinder
    , bodyInfo :: TypeInfo b
    }

  typeInfo = do
    bodyInfo' <- typeInfo @b
    pure ForAllInfo
      { quantInfo = quantifier @a
      , bodyInfo = bodyInfo'
      }

  reifiedTy ForAllInfo { .. } = mkForAllTy quantInfo $ reifiedTy bodyInfo

  reify info subst body = do
    let ty = substTy subst $ reifiedTy info
    pure $ mkLam ty \arg -> do
      let tv = binderVar $ quantInfo info
      subst' <- extendSubst subst tv arg
      reify (bodyInfo info) subst' body

  interpret info subst fun = do
    let body = do
          fun' <- fun
          let arg = mkTyVarTy $ binderVar (quantInfo info)
          let arg' = pure $ mkType arg
          mkApp fun' arg'

    interpret (bodyInfo info) subst body

instance (Quantifier a, ReifyBuiltin b) => ReifyBuiltin (a +> b) where
  builtinTypeInfo = ForAllInfo
    { quantInfo = quantifier @a
    , bodyInfo = builtinTypeInfo @b
    }

-- | Function arrow reify marker.
data a ~> b
infixr ~>

instance (Reify a, Reify b) => Reify (a ~> b) where
  type InterpRep (a ~> b) = Eval (InterpRep a) -> Eval (InterpRep b)

  data TypeInfo (a ~> b) = FunInfo
    { argInfo :: TypeInfo a
    , resInfo :: TypeInfo b
    }

  typeInfo = do
    argInfo' <- typeInfo @a
    resInfo' <- typeInfo @b
    pure FunInfo
      { argInfo = argInfo'
      , resInfo = resInfo'
      }

  reifiedTy FunInfo { .. } = do
    let argTy = reifiedTy argInfo
    let resTy = reifiedTy resInfo
    GHC.mkFunTy GHC.FTF_T_T GHC.ManyTy argTy resTy

  reify info subst fun = do
    let ty = substTy subst $ reifiedTy info
    pure $ mkLam ty \arg -> do
      fun' <- fun
      let arg' = interpret (argInfo info) subst arg
      let result = fun' arg'
      reify (resInfo info) subst result

  interpret info subst fun = do
    pure \arg -> do
      fun' <- fun
      let arg' = reify (argInfo info) subst arg
      let result = mkApp fun' arg'
      interpret (resInfo info) subst result

instance (ReifyBuiltin a, ReifyBuiltin b) => ReifyBuiltin (a ~> b) where
  builtinTypeInfo = FunInfo
    { argInfo = builtinTypeInfo @a
    , resInfo = builtinTypeInfo @b
    }

-- | Sized integer primitive reify marker.
--
-- Note that this is not restricted to just machine words (i.e. it can be any
-- size).
-- TODO: It is not clear that this is a Pantomime primitive... Perhaps change
-- the name a bit? 'RPIntN' maybe works (similar to how the Haskell version is
-- 'RHIntN'). Idk, it's mostly an issue for other types e.g. Integer and the
-- Pantomime symbolic Integer primitive.
data RIntN n

instance Quantifier n => Reify (RIntN n) where
  type InterpRep (RIntN n) = SomeBV (IntN S)

  data TypeInfo (RIntN n) = IntNInfo
    { intNTcInfo :: TyCon
    , intNNInfo :: TyVar
    }

  typeInfo = do
    name <- thNameToGhcName ''Primitive.IntN
    tc <- lookupTyCon name
    pure IntNInfo
      { intNTcInfo = tc
      , intNNInfo = binderVar $ quantifier @n
      }

  reifiedTy IntNInfo { .. } = do
    mkTyConApp intNTcInfo [mkTyVarTy intNNInfo]

  reify info subst value = do
    let ty = substTy subst $ reifiedTy info
    SomeBV value' <- value
    pure $ mkLit (mkIntN value' ty)

  interpret info subst value = do
    let reqTy = substTy subst $ reifiedTy info
    value >>= \case
      Lit (Int value' ty) | eqType ty reqTy -> pure $ SomeBV value'
      _ -> throwError' ()

-- | KnownNat constraint reify marker.
data RKnownNat n

instance Quantifier n => Reify (RKnownNat n) where
  type InterpRep (RKnownNat n) = InterpRep RNatural

  data TypeInfo (RKnownNat n) = KnownNatInfo
    { knownNatTcInfo :: TyCon
    , knownNatNInfo :: TyVar
    }

  typeInfo = do
    name <- thNameToGhcName ''KnownNat
    tc <- lookupTyCon name
    pure KnownNatInfo
      { knownNatTcInfo = tc
      , knownNatNInfo = binderVar $ quantifier @n
      }

  reifiedTy KnownNatInfo { .. } = do
    mkTyConApp knownNatTcInfo [mkTyVarTy knownNatNInfo]

  reify info subst value = do
    let tc = knownNatTcInfo info
    let tv = substTyVar subst $ knownNatNInfo info
    (_, co) <- whyFail' () $ instNewTyCon_maybe tc [tv]
    inner <- reify NaturalInfo subst value
    mkCast inner $ mkSymCo co

  interpret info subst value = do
    let reqTy = substTy subst $ reifiedTy info

    -- Unwrap the KnownNat typeclass (which is a cast over a Natural).
    body <- value >>= \case
      Cast body co | eqType reqTy $ coercionRKind co -> pure body
      _ -> throwError' ()

    interpret NaturalInfo subst $ liftUnion body

-- | Natural reify marker.
data RNatural

instance Reify RNatural where
  type InterpRep RNatural = Either (SomeBV (WordN S)) ()

  data TypeInfo RNatural = NaturalInfo

  typeInfo = pure NaturalInfo

  reifiedTy _ = naturalTy

  reify _info _subst expr = do
    expr >>= \case
      Left (SomeBV value) -> do
        -- FIXME: Give proper platform size
        let dc = mkLit $ mkDataCon @64 naturalNSDataCon
        let arg = pure $ mkLit (mkWordN value wordPrimTy)
        mkApp dc arg
      Right _value -> do
        let _dc = mkLit $ mkDataCon @64 naturalNBDataCon
        -- let arg = pure $ mkLit (mkByteArray value byteArrayPrimTy)
        -- mkApp dc arg
        -- FIXME: Implement this once we have byte array primitives.
        undefined

  interpret _info _subst expr = do
    -- Gather the arguments.
    (spine, args) <- collectArgs <$> expr

    -- Check whether the spine is indeed a natural datacon.
    dc <- case spine of
      Lit (DataCon tag tc)
        | tc == naturalTyCon 
        , Just dc <- concreteDataCon tag tc -> pure dc
      _ -> throwError' ()

    -- All natural DataCon have only one argument exactly. Note that we also
    -- force it here already.
    arg <- case args of
      [arg] -> arg
      _ -> throwError' ()

    if
      | dc == naturalNSDataCon
      , Lit (Word value ty) <- arg
      -- TODO: We could consider turning the Int into a ByteArray, such that we
      -- have a uniform way of interpreting a Natural.
      , eqType ty wordPrimTy -> pure $ Left (SomeBV value)

      | dc == naturalNBDataCon
      -- FIXME: We should have a ByteArray primitive to match on here!
      , Lit _ <- arg -> pure $ Right ()

      | otherwise -> throwError' ()

instance ReifyBuiltin RNatural where
  builtinTypeInfo = NaturalInfo

-- | Integer reify marker.
data RInteger

instance Reify RInteger where
  type InterpRep RInteger = Either (SomeBV (IntN S)) ()

  data TypeInfo RInteger = IntegerInfo

  typeInfo = pure IntegerInfo

  reifiedTy _ = integerTy

  reify _info _subst expr = do
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

  interpret _info _subst expr = do
    -- Gather the arguments.
    (spine, args) <- collectArgs <$> expr

    -- Check whether the spine is indeed a natural datacon.
    dc <- case spine of
      Lit (DataCon tag tc)
        | tc == integerTyCon
        , Just dc <- concreteDataCon tag tc -> pure dc
      _ -> throwError' ()

    -- All natural DataCon have only one argument exactly. Note that we also
    -- force it here already.
    arg <- case args of
      [arg] -> arg
      _ -> throwError' ()

    if
      | dc == integerISDataCon
      , Lit (Int value ty) <- arg
      -- TODO: We could consider turning the Int into a ByteArray, such that we
      -- have a uniform way of interpreting a Integer.
      , eqType ty intPrimTy -> pure $ Left (SomeBV value)

      | dc == integerIPDataCon
      -- FIXME: We should have a ByteArray primitive to match on here!
      , Lit _ <- arg -> pure $ Right ()

      | dc == integerINDataCon
      -- FIXME: We should have a ByteArray primitive to match on here!
      , Lit _ <- arg -> pure $ Right ()

      | otherwise -> throwError' ()

instance ReifyBuiltin RInteger where
  builtinTypeInfo = IntegerInfo

-- | Reify marker for Haskell sized integer primitives.
data RHIntN (n :: Nat)

instance
  ( KnownNat n
  , (n == 8 || n == 16 || n == 32 || n == 64) ~ True
  ) => Reify (RHIntN n) where
  type InterpRep (RHIntN n) = IntN S n

  data TypeInfo (RHIntN n) = HIntNInfo TyCon

  typeInfo = pure builtinTypeInfo

  reifiedTy (HIntNInfo tc) = mkTyConTy tc

  reify info _subst value = do
    value' <- value
    let ty = reifiedTy info
    pure $ mkLit (mkIntN value' ty)

  interpret info _subst value = value >>= \case
    Lit (Int @m value' ty)
      | Just Refl <- eqT @n @m
      , eqType ty $ reifiedTy info -> pure value'
    _ -> throwError' ()

instance
  ( KnownNat n
  , (n == 8 || n == 16 || n == 32 || n == 64) ~ True
  ) => ReifyBuiltin (RHIntN n) where

  builtinTypeInfo = HIntNInfo $ case natVal @n Proxy of
    8 -> int8PrimTyCon
    16 -> int16PrimTyCon
    32 -> int32PrimTyCon
    64 -> int64PrimTyCon
    _ -> error "unreachable due to typeclass constraint"

-- | Reify marker for the Haskell platform sized integer primitives.
data RHIntPW (n :: Nat)

instance KnownNat n => Reify (RHIntPW n) where
  type InterpRep (RHIntPW n) = IntN S n

  data TypeInfo (RHIntPW n) = HIntPWInfo TyCon

  typeInfo = pure builtinTypeInfo

  reifiedTy (HIntPWInfo tc) = mkTyConTy tc

  reify info _subst value = do
    value' <- value
    let ty = reifiedTy info
    pure $ mkLit (mkIntN value' ty)

  interpret info _subst value = value >>= \case
    Lit (Int @m value' ty)
      | Just Refl <- eqT @n @m
      , eqType ty $ reifiedTy info -> pure value'
    _ -> throwError' ()

instance KnownNat n => ReifyBuiltin (RHIntPW n) where
  builtinTypeInfo = HIntPWInfo intPrimTyCon

-- | Reify marker for Haskell sized integer primitives.
data RHWordN (n :: Nat)

instance
  ( KnownNat n
  , (n == 8 || n == 16 || n == 32 || n == 64) ~ True
  ) => Reify (RHWordN n) where
  type InterpRep (RHWordN n) = WordN S n

  data TypeInfo (RHWordN n) = HWordNInfo TyCon

  typeInfo = pure builtinTypeInfo

  reifiedTy (HWordNInfo tc) = mkTyConTy tc

  reify info _subst value = do
    value' <- value
    let ty = reifiedTy info
    pure $ mkLit (mkWordN value' ty)

  interpret info _subst value = value >>= \case
    Lit (Word @m value' ty)
      | Just Refl <- eqT @n @m
      , eqType ty $ reifiedTy info -> pure value'
    _ -> throwError' ()

instance
  ( KnownNat n
  , (n == 8 || n == 16 || n == 32 || n == 64) ~ True
  ) => ReifyBuiltin (RHWordN n) where

  builtinTypeInfo = HWordNInfo $ case natVal @n Proxy of
    8 -> word8PrimTyCon
    16 -> word16PrimTyCon
    32 -> word32PrimTyCon
    64 -> word64PrimTyCon
    _ -> error "unreachable due to typeclass constraint"

-- | Reify marker for the Haskell platform sized integer primitives.
data RHWordPW (n :: Nat)

instance KnownNat n => Reify (RHWordPW n) where
  type InterpRep (RHWordPW n) = WordN S n

  data TypeInfo (RHWordPW n) = HWordPWInfo TyCon

  typeInfo = pure builtinTypeInfo

  reifiedTy (HWordPWInfo tc) = mkTyConTy tc

  reify info _subst value = do
    value' <- value
    let ty = reifiedTy info
    pure $ mkLit (mkWordN value' ty)

  interpret info _subst value = value >>= \case
    Lit (Word @m value' ty)
      | Just Refl <- eqT @n @m
      , eqType ty $ reifiedTy info -> pure value'
    _ -> throwError' ()

instance KnownNat n => ReifyBuiltin (RHWordPW n) where
  builtinTypeInfo = HWordPWInfo wordPrimTyCon

-- | Type variable alpha of kind Nat.
data AlphaNat

instance Quantifier AlphaNat where
  quantifier = do
    let tv = setTyVarKind alphaTyVar naturalTy
    Bndr tv Specified

-- | Type variable alpha of kind 'TYPE (BoxedRep l)'.
data AlphaBoxed l

instance Quantifier l => Quantifier (AlphaBoxed l) where
  quantifier = do
    let levity = binderVar $ quantifier @l
    let rep = mkTyConApp boxedRepDataConTyCon [mkTyVarTy levity]
    let kind = mkTyConApp tYPETyCon [rep]
    let tv = setTyVarKind alphaTyVar kind
    Bndr tv Specified

-- | Type variable beta of kind levity.
data BetaLevity

instance Quantifier BetaLevity where
  quantifier = Bndr levPolyBetaTyVar Specified

liftF1'
  :: Applicative f
  => (a -> b)
  -> f (f a -> f b)
liftF1' = pure . fmap

liftF2
  :: Applicative f
  => (f a -> f b -> f c)
  -> f (f a -> f (f b -> f c))
liftF2 f = pure $ pure . f

liftF2'
  :: Applicative f
  => (a -> b -> c)
  -> f (f a -> f (f b -> f c))
liftF2' = liftF2 . liftA2

liftF3
  :: Applicative f
  => (f a -> f b -> f c -> f d)
  -> f (f a -> f (f b -> f (f c -> f d)))
liftF3 f = pure $ liftF2 . f

liftF3'
  :: Applicative f
  => (a -> b -> c -> d)
  -> f (f a -> f (f b -> f (f c -> f d)))
liftF3' = liftF3 . liftA3
