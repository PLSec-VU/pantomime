{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module Pantomime.Literal
  -- | The primary export of this module.
  --
  -- This contains the 'Literal' itself as well as its type and typeclass
  -- constraint.
  ( Literal (Literal, Bool, Integer, BitVec, Array)
  , LiteralTypeable (..)
  , HasDict (..)
  , literalTypeOf
  , LiteralType (..)
  , eqLiteralType
  , SomeLiteralType (..)

  -- TODO: Where to place this?
  , SymBitVec

  -- | Conversion between 'LiteralType' and 'Type'.
  , BuiltInTyCon (..)
  , embedLitTy
  , reifyLitTy
  ) where

import Control.Applicative (Alternative(..))
import Control.Monad ((>=>))

import Data.Constraint
import Data.Functor.Identity (Identity(..))
import Data.Maybe (isJust)
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable, type (:~:) (..), eqT)

import Effectful
import Effectful.Context
import Effectful.Error.Static
import Effectful.GHC.External

import GHC.Core.Reduction (Reduction(..))
import GHC.Core.FamInstEnv (normaliseType)
import GHC.Plugins
  ( Type
  , TyCon
  , CoercionN
  , Role (..)
  , mkTyConTy
  , mkNumLitTy
  , mkTyConApp
  , splitTyConApp_maybe
  , isNumLitTy
  )
import GHC.TypeLits (SomeNat (..), natVal, someNatVal)

import Grisette
  ( SymBool
  , SymWordN
  , SymInteger
  , Solvable
  , ConRep(..)
  , LinkedRep
  , Mergeable (..)
  , SimpleMergeable (..)
  , MergingStrategy (..)
  , EvalSym (..)
  )
-- TODO: Remove internal import once we fix Grisette API.
import Grisette.Internal.SymPrim.Prim.Term (SupportedNonFuncPrim)
import Grisette.Internal.SymPrim.SymArray (SymArray)

import Pantomime.Dict (posNat)
import Pantomime.Util (KnownPos, failWith)
import Pantomime.Grisette.Mergeable (impossible)

class
  -- TODO: I'm not sure if I should have these here or somewhere else, as we can
  -- also reify them from just LiteralType. I guess this is the most ergonomic?
  ( SupportedNonFuncPrim (ConType a)
  , LinkedRep (ConType a) a
  , Solvable (ConType a) a
  , SimpleMergeable a
  , EvalSym a
  , Typeable a
  )
  => LiteralTypeable a where
  literalType :: LiteralType a

instance LiteralTypeable SymBool where
  literalType = BoolType

instance LiteralTypeable SymInteger where
  literalType = IntegerType

instance KnownPos n => LiteralTypeable (SymBitVec n) where
  literalType = BitVecType

instance
  ( LiteralTypeable k
  , LiteralTypeable v
  )
  => LiteralTypeable (SymArray k v) where
  literalType = ArrayType literalType literalType

-- | Get the 'LiteralType' for the given instance.
literalTypeOf :: LiteralTypeable a => a -> LiteralType a
literalTypeOf _ = literalType

-- | The type of literals supported within the symbolic executor.
--
-- This is like a version of 'TypeRep' for a fixed domain of types.
data LiteralType a where
  BoolType
    :: LiteralType SymBool
  IntegerType
    :: LiteralType SymInteger
  BitVecType
    :: KnownPos n
    => LiteralType (SymBitVec n)
  ArrayType
    :: LiteralType k
    -> LiteralType v
    -> LiteralType (SymArray k v)

instance Eq (LiteralType a) where
  (==) _ _ = True

instance Ord (LiteralType a) where
  compare _ _ = EQ

instance Mergeable (LiteralType a) where
  rootStrategy = SimpleStrategy mrgIte

instance SimpleMergeable (LiteralType a) where
  mrgIte _ value _ = value

instance HasDict (LiteralTypeable a) (LiteralType a) where
  evidence = \case
    BoolType -> Dict
    IntegerType -> Dict
    BitVecType -> Dict
    ArrayType keyTy valTy -> runIdentity do
      Dict <- pure $ evidence keyTy
      Dict <- pure $ evidence valTy
      pure Dict

eqLiteralType :: LiteralType a -> LiteralType b -> Maybe (a :~: b)
eqLiteralType = \cases
  BoolType BoolType -> pure Refl
  IntegerType IntegerType -> pure Refl
  (BitVecType @nl) (BitVecType @nr) -> do
    Refl <- eqT @nl @nr
    pure Refl
  (ArrayType keyTyL valTyL) (ArrayType keyTyR valTyR) -> do
    Refl <- eqLiteralType keyTyL keyTyR
    Refl <- eqLiteralType valTyL valTyR
    pure Refl
  _ _ -> empty

data SomeLiteralType where
  SomeLiteralType :: !(LiteralType a) -> SomeLiteralType

instance Eq SomeLiteralType where
  SomeLiteralType lhs == SomeLiteralType rhs = isJust $ eqLiteralType lhs rhs

instance Ord SomeLiteralType where
  compare (SomeLiteralType lhs) (SomeLiteralType rhs) = case (lhs, rhs) of
    (BoolType, BoolType) -> EQ
    (BoolType, _) -> GT

    (IntegerType, BoolType) -> LT
    (IntegerType, IntegerType) -> EQ
    (IntegerType, _) -> GT

    (BitVecType, BoolType) -> LT
    (BitVecType, IntegerType) -> LT
    (BitVecType @nl, BitVecType @nr) -> do
      let nL = natVal @nl Proxy
      let nR = natVal @nr Proxy
      compare nL nR
    (BitVecType, ArrayType _ _) -> GT

    (ArrayType keyTyL valTyL, ArrayType keyTyR valTyR) -> do
      let lhs' = (SomeLiteralType keyTyL, SomeLiteralType valTyL)
      let rhs' = (SomeLiteralType keyTyR, SomeLiteralType valTyR)
      compare lhs' rhs'
    (ArrayType _ _, _) -> LT

instance Mergeable SomeLiteralType where
  rootStrategy = SortedStrategy id $ \_ -> SimpleStrategy \_ value _ -> value

-- TODO: Not sure where to keep this. I like the uniformity of having this, so
-- I'll keep it here for now. Perhaps it should go into Util?
-- | Symbolic bitvector type.
type SymBitVec = SymWordN

-- | Symbolic literals supported by the symbolic execution engine.
data Literal where
  Literal :: LiteralType a -> a -> Literal

instance Mergeable Literal where
  rootStrategy = SortedStrategy
    (\(Literal ty _value) -> SomeLiteralType ty)
    \(SomeLiteralType ty) -> SimpleStrategy \cases
      scrut (Literal lty lval) (Literal rty rval)
        | Just Refl <- eqLiteralType ty lty
        , Just Refl <- eqLiteralType ty rty
        , Dict <- evidence ty -> do
          Literal ty $ mrgIte scrut lval rval
      _ _ _ -> impossible

instance EvalSym Literal where
  evalSym fill model (Literal ty value) = runIdentity do
    Dict <- pure $ evidence ty
    let value' = evalSym fill model value
    pure $ Literal ty value'

pattern Bool :: SymBool -> Literal
pattern Bool value = Literal BoolType value

pattern Integer :: SymInteger -> Literal
pattern Integer value = Literal IntegerType value

pattern BitVec :: () => KnownPos n => SymBitVec n -> Literal
pattern BitVec value = Literal BitVecType value

pattern Array
  :: () =>
   ( LiteralTypeable k
   , LiteralTypeable v
   )
  => SymArray k v
  -> Literal
pattern Array value <- (viewArray -> Just (ViewArray value))
  where
    Array value = Literal (ArrayType literalType literalType) value

{-# COMPLETE Bool, Integer, BitVec, Array #-}

-- | Helper data type for pattern synonym 'Array'.
data ViewArray where
  ViewArray
    :: forall k v.
     ( LiteralTypeable k
     , LiteralTypeable v
     )
    => SymArray k v
    -> ViewArray

-- | Helper view pattern for pattern synonym 'Array'.
viewArray :: Literal -> Maybe ViewArray
viewArray = \case
  Literal (ArrayType keyTy valTy) value -> do
    Dict <- pure $ evidence keyTy
    Dict <- pure $ evidence valTy
    pure $ ViewArray value
  _ -> empty

-- | Built-in type constructors.
data BuiltInTyCon where
  BuiltInTyCon ::
    { tcBool :: TyCon
    , tcInteger :: TyCon
    , tcBitVec :: TyCon
    , tcArray :: TyCon
    } -> BuiltInTyCon

-- | Convert a 'LiteralType' into a normal Haskell 'Type'.
embedLitTy
  :: Context Reader BuiltInTyCon :> es
  => LiteralType a
  -> Eff es Type
embedLitTy ty = do
  -- TODO: I feel like this is not the best way to have the effect. Probably we
  -- just want to wrap the other lookup effect stack!
  BuiltInTyCon { .. } <- get
  case ty of
    BoolType -> pure $ mkTyConTy tcBool
    IntegerType -> pure $ mkTyConTy tcInteger
    BitVecType @n -> do
      let nTy = mkNumLitTy $ natVal @n Proxy
      pure $ mkTyConApp tcBitVec [nTy]
    ArrayType keyTy valTy -> do
      keyTy' <- embedLitTy keyTy
      valTy' <- embedLitTy valTy
      pure $ mkTyConApp tcArray [keyTy', valTy']

-- | Fetch a 'LiteralType' from a GHC 'Type', if possible.
--
-- This additionally return a nominal coercion for all type-families that were
-- reduced.
reifyLitTy
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => Type
  -> Eff es (CoercionN, SomeLiteralType)
reifyLitTy ty = do
  fam <- getFamInstEnvs
  -- NOTE: Altough normalising the entire term is slow, we only really do this
  -- if we actually force the entire type within reifyLitType (in which case, we
  -- needed to normalise anyway).
  let Reduction co ty' = normaliseType fam Nominal ty
  lty <- reifyLitType' ty'
  pure (co, lty)

-- | Helper function for 'reifyLitType'.
--
-- This will reify the 'LiteralType' from a GHC 'Type' only if it is free from
-- any type families or aliases.
reifyLitType'
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => Type
  -> Eff es SomeLiteralType
reifyLitType' ty = do
  -- TODO: We should fix the recursive callstack grow!
  (tc, targs) <- failWith () $ splitTyConApp_maybe ty
  BuiltInTyCon { .. } <- get
  if
    | tc == tcBool
    , [] <- targs -> pure $ SomeLiteralType BoolType

    | tc == tcInteger
    , [] <- targs -> pure $ SomeLiteralType IntegerType

    | tc == tcBitVec
    , [narg] <- targs -> do
      let knownNatTy = isNumLitTy >=> someNatVal
      SomeNat @n _ <- failWith () $ knownNatTy narg
      Dict <- failWith () $ posNat @n
      pure $ SomeLiteralType (BitVecType @n)

    | tc == tcArray
    , [keyTy, valTy] <- targs -> do
      SomeLiteralType keyTy' <- reifyLitType' keyTy
      SomeLiteralType valTy' <- reifyLitType' valTy
      pure $ SomeLiteralType (ArrayType keyTy' valTy')

    | otherwise -> throwError ()
