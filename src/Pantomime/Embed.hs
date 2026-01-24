{-# LANGUAGE PatternSynonyms #-}

module Pantomime.Embed
  ( Ty (..)
  , Repr
  , Reflect (..)
  , STy (..)
  , embed
  , embed'
  , project
  , project'
  ) where

import Data.Char (ord, chr)
import Data.Data (Proxy(..))

import Effectful
import Effectful.Error.Static (Error, HasCallStack, throwError)
import Effectful.Context
import Effectful.GHC.External (HasFamInstEnvs, getFamInstEnvs)

import GHC.Builtin.Uniques (mkAlphaTyVarUnique)
import GHC.Core.Type (substTy)
import GHC.Core.FamInstEnv (normaliseType)
import GHC.Core.Reduction (Reduction(..))
import GHC.Core.TyCo.Rep (Type(..), TyLit (..))
import GHC.Plugins
  ( Subst
  , FunTyFlag (..)
  , VarBndr (..)
  , ForAllTyFlag (..)
  , Kind
  , TyVar
  , Role (..)
  , CoercionN
  , mkTyConTy
  , mkTyConApp
  , mkFunTy
  , mkForAllTy
  , mkTyVar
  , mkTyConAppCo
  , mkInternalName
  , mkTyVarOcc
  , mkTyVarTy
  , mkSubCo
  , noSrcSpan
  , extendTvSubst
  , naturalTy
  , pattern ManyTy
  )
import GHC.TypeLits
  ( Nat
  , KnownNat
  , TypeError
  , ErrorMessage (..)
  , SomeNat
  , someNatVal
  , natVal
  )

import Grisette (SymInteger, SymBool)

import Pantomime.Expr
  ( Expr (..)
  , Literal (..)
  , Eval
  , EvalExpr
  , mkLit
  , mkBool
  , mkInteger
  , mkLam
  , mkApp
  , mkType
  , mkCast
  , mkBitVec
  , forceTy
  , liftEff
  , throwE
  )
import Pantomime.Util (SomeBitVec (..), SymBitVec)
import Pantomime.Literal (BuiltInTyCon (..))

data Ty where
  BoolTy :: Ty
  IntegerTy :: Ty
  BitVecTy :: Ty -> Ty
  (:->) :: Ty -> Ty -> Ty
  (:.) :: (Nat, Ty) -> Ty -> Ty
  TyVar :: Nat -> Ty -> Ty
  -- TODO: Ideally, we remove the dependency on 'Natural' from 'base'
  -- completely. We'll have to swap away from the standard KnownNat for this.
  -- This is possible, but would require a type check plugin to fill in an
  -- equivalent KnownNat that uses pantomime Integer. For now, we just magically
  -- reify the natural from the type. This way, we don't actually have to know
  -- the representation of natural. Note, the representation of natural is
  -- fragile as a user can dictate it. Hence, a dependency on this would be bad.
  NaturalTy :: Ty
  KnownNatTy :: Ty -> Ty
  -- TYPE :: Ty -> Ty
  -- RuntimeRep :: Type

class Reflect ty where
  reflect :: STy ty

instance Reflect BoolTy where
  reflect = SBoolTy

instance Reflect IntegerTy where
  reflect = SIntegerTy

instance Reflect n => Reflect (BitVecTy n) where
  reflect = SBitVecTy reflect

instance (Reflect a, Reflect b) => Reflect (a :-> b) where
  reflect = SLambda reflect reflect

instance (KnownNat n, Reflect a, Reflect b) => Reflect ('(n, a) :. b) where
  reflect = SForall reflect reflect

instance (KnownNat n, Reflect k) => Reflect ('TyVar n k) where
  reflect = STyVar reflect

instance Reflect NaturalTy where
  reflect = SNaturalTy

instance Reflect n => Reflect (KnownNatTy n) where
  reflect = SKnownNatTy reflect

type family Repr a es where
  Repr BoolTy _ = SymBool
  Repr IntegerTy _ = SymInteger
  Repr (BitVecTy _) _ = SomeBitVec SymBitVec
  Repr (a :-> b) es = Eval es (Repr a es) -> Eval es (Repr b es)
  -- Whilst we could technically extract the 'Repr' of the forall argument, it
  -- would be very cumbersome as it is a type and not a term. Instead, we just
  -- leave it abstractly as a 'Type' for now. Note that we don't need to wrap
  -- it in 'Eval' as forcing a 'Type' should always be possible.
  Repr (_ :. b) es = Type -> Eval es (Repr b es)
  Repr ('TyVar _ _) es = Expr es
  Repr NaturalTy _ = TypeError (Text "'Natural' is not a native Pantomime type and thus has no built-in representation.")
  Repr (KnownNatTy _) _ = SomeNat

data STy a where
  SBoolTy :: STy 'BoolTy
  SIntegerTy :: STy 'IntegerTy
  SBitVecTy :: STy n -> STy ('BitVecTy n)
  SLambda :: STy a -> STy b -> STy (a ':-> b)
  SForall :: KnownNat n => STy k -> STy b -> STy ('(n, k) ':. b)
  STyVar :: KnownNat n => STy k -> STy ('TyVar n k)
  SNaturalTy :: STy 'NaturalTy
  SKnownNatTy :: STy n -> STy ('KnownNatTy n)

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
  SBitVecTy n -> do
    SomeBitVec bv <- repr
    let lit = mkLit $ mkBitVec bv
    co <- liftEff $ mkBitVecCo n
    mkCast lit co
  SLambda aty rty -> do
    -- Gather the type for the lambda.
    ty <- liftEff $ embedSTy sty
    let ty' = substTy subst ty

    pure $ mkLam ty' \arg -> do
      let arg' = project' subst aty arg
      fun <- repr
      embed' subst rty $ fun arg'
  SForall @n aty rty -> do
    -- Gather the type for the lambda.
    ty <- liftEff $ embedSTy sty
    let ty' = substTy subst ty

    pure $ mkLam ty' \arg -> do
      -- Gather the function and argument.
      fun <- repr
      arg' <- liftEff $ forceTy arg

      -- Extend the substition.
      tv <- liftEff $ mkTemplateTyVar' @n aty
      let subst' = extendTvSubst subst tv arg'

      -- Construct the final expression.
      embed' subst' rty $ fun arg'
  STyVar _kind -> repr
  -- TODO: I feel like I should be able to deduce this is unreachable due to a
  -- type-family instance not existing.
  SNaturalTy -> throwE ()
  SKnownNatTy _n -> throwE ()

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
  SBitVecTy n -> do
    co <- liftEff $ mkBitVecCo n
    inner <- expr
    expr' <- mkCast inner $ mkSubCo co
    case expr' of
      Lit (BitVec bv) -> pure $ SomeBitVec bv
      _ -> throwE ()
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
  STyVar _kind -> expr
  SNaturalTy -> throwE ()
  SKnownNatTy n -> liftEff do
    n' <- embedSTy n
    fam <- getFamInstEnvs
    let Reduction _ ty = normaliseType fam Nominal n'
    case ty of
      LitTy (NumTyLit i) | Just val <- someNatVal i -> pure val
      _ -> throwError ()

embedSTy
  :: HasCallStack
  => Context Reader BuiltInTyCon :> es
  => STy a
  -> Eff es Type
embedSTy ty = do
  BuiltInTyCon { .. } <- get
  case ty of
    SBoolTy -> pure $ mkTyConTy tcBool
    SIntegerTy -> pure $ mkTyConTy tcInteger
    SBitVecTy n -> do
      n' <- embedSTy n
      pure $ mkTyConApp tcBitVec [n']
    SLambda aty rty -> do
      aty' <- embedSTy aty
      rty' <- embedSTy rty
      pure $ mkFunTy FTF_T_T ManyTy aty' rty'
    SForall @n aty rty -> do
      tv <- mkTemplateTyVar' @n aty
      let bndr = Bndr tv Specified
      rty' <- embedSTy rty
      pure $ mkForAllTy bndr rty'
    STyVar @n kind -> do
      tv <- mkTemplateTyVar' @n kind
      pure $ mkTyVarTy tv
    SNaturalTy -> pure $ naturalTy
    SKnownNatTy n -> do
      n' <- embedSTy n
      pure $ mkTyConApp tcKnownNat [n']

mkTemplateTyVar'
  :: forall n a es
   . HasCallStack
  => KnownNat n
  => Context Reader BuiltInTyCon :> es
  => STy a
  -> Eff es TyVar
mkTemplateTyVar' kind = do
  let n = fromInteger $ natVal @n Proxy
  -- TODO: This is mutually recursive with 'embedSTy'. We should restrict
  -- callstack growth.
  kind' <- embedSTy kind
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

-- | Construct the coercion which to cast a bitvector with based on any nominal
-- reduction on the given size type.
mkBitVecCo
  :: HasCallStack
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => STy n
  -> Eff es CoercionN
mkBitVecCo sn = do
  -- Reduce the type of the bitvector size.
  n <- embedSTy sn
  fam <- getFamInstEnvs
  let Reduction co _ = normaliseType fam Nominal n

  -- Construct the coercion with which to cast the expression.
  tc <- gets tcBitVec
  pure $ mkTyConAppCo Nominal tc [co]

