module Pantomime.Interpret
  ( interpPlus
  ) where

import Pantomime.Expr
  ( Type
  , Subst
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
  , emptySubst
  , extendSubst
  , substTy
  , substTyVar
  , throwError'
  , whyFail'
  , dbgE
  , pprArg
  )
import Pantomime.Prim qualified as Primitive
import Pantomime.Grisette.BitVector
import Pantomime.Grisette.SomeBV (SomeBV (..))

import GHC.TypeNats (KnownNat)
import GHC.Builtin.Types.Prim (alphaTyVar, wordPrimTy)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Plugins qualified as GHC
import GHC.Plugins
  ( Name
  , TyCon
  , TyVar
  , ForAllTyBinder
  , ForAllTyFlag (..)
  , VarBndr (..)
  , Id
  , mkTyConApp
  , mkSymCo
  , setTyVarKind
  , naturalTy
  , mkTyVarTy
  , mkForAllTy
  , binderVar
  , coercionRKind
  , instNewTyCon_maybe
  , naturalTyCon
  , naturalNBDataCon
  , naturalNSDataCon
  )

import Language.Haskell.TH qualified as TH

import Data.Typeable (eqT, type (:~:) (..))

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
    -> Subst
    -> Eval Expr
    -> Eval (InterpRep a)

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
    fun' <- fun
    pure $ mkLam ty \arg -> do
      let arg' = interpret (argInfo info) subst arg
      let result = fun' arg'
      reify (resInfo info) subst result

  interpret info subst fun = do
    fun' <- fun
    pure \arg -> do
      let arg' = reify (argInfo info) subst arg
      let result = mkApp fun' arg'
      interpret (resInfo info) subst result

-- | Sized integer primitive reify marker.
--
-- Note that this is not restricted to just machine words (i.e. it can be any
-- size).
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
      _ -> do
        dbgE $ pprArg id value
        throwError' ()

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

class Quantifier a where
  quantifier :: ForAllTyBinder

-- | Type variable alpha of kind Nat.
data AlphaNat

instance Quantifier AlphaNat where
  quantifier = do
    let tv = setTyVarKind alphaTyVar naturalTy
    Bndr tv Specified

liftF2
  :: Applicative f
  => (f a -> f b -> f c)
  -> f a -> f (f b -> f c)
liftF2 f = pure . f

liftF3
  :: Applicative f
  => (f a -> f b -> f c -> f d)
  -> f a -> f (f b -> f (f c -> f d))
liftF3 f = pure . liftF2 . f

type BinaryIntN
  =  AlphaNat
  +> RKnownNat AlphaNat
  ~> RIntN AlphaNat
  ~> RIntN AlphaNat
  ~> RIntN AlphaNat

interpPlus
  :: forall es
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Eff es (Id, Eval Expr)
interpPlus = do
  name <- thNameToGhcName 'Primitive.plusIntN
  var <- lookupId name
  info <- typeInfo
  let interpreted :: Eval (InterpRep BinaryIntN)
      interpreted = pure . liftF3 $ \c x y -> do
        -- We force the KnownNat constraint for faithful interpretation. We
        -- don't need to use it however as bitvectors already track their size
        -- inside of an expression.
        _ <- c
        SomeBV @n x' <- x
        SomeBV @m y' <- y
        Refl <- whyFail' () $ eqT @n @m
        pure $ SomeBV (x' + y')
  let body = reify @BinaryIntN info emptySubst interpreted
  pure (var, body)
