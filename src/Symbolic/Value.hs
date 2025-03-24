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

module Symbolic.Value
  ( Value (..)
  , EvalError (..)
  , mkCast'
  , accessField
  , typedValue
  , invalidValue
  , nArity

  , applyValue
  , applyValues
  , cmpValue
  , iteValue

  , Primitive (..)
  , typedPrimitive
  , cmpPrimitive
  , itePrimitive
  ) where

import GHC.Plugins hiding (empty)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Builtin.Types.Prim

import Grisette.SymPrim
import Grisette.Unified (EvalModeTag (..))
import Grisette (Solvable (..), Mergeable)

import Control.Monad (unless, foldM)
import Control.Monad.Except (MonadError (..))

import Symbolic.Util
import Symbolic.WordSize
import Symbolic.Runtime
import Symbolic.ADT
import GHC.Platform (PlatformWordSize)
import Grisette.Lib.Control.Monad.Except (mrgThrowError)
import Symbolic.Identifier

-- data Func m n where
--   SFunc :: Type -> SymWordN64 -> Func m n
--   CFunc :: Type -> (Value m n -> m (Value m n)) -> Func m n

-- TODO: Could we adjust n to be a DataKind of the actual word size data type
-- from GHC? To me that seems a lot cleaner, as it represents more
-- accurately what values n should range over are exactly.
data Value m ws where
  -- TODO: Add support for Char
  -- TODO: Add support for ByteArray (as this is how big integers are
  -- implemented under the hood).
  -- TODO: Add support for symbolic (higher order) functions.
  -- Char :: RuntimeValue (SymWordN 31) -> Value m n
  -- BigNat :: RuntimeValue SymInteger -> Value m n
  Primitive :: Primitive ws -> Value m ws
  -- TODO: I think it would be nice to have an ADT be already its TyCon and
  -- Type arguments split. This prevents us from making some class of ill-formed
  -- ADTs.
  Data :: ADT S -> Value m ws
  -- TODO: I don't really like the prime on the name of Cast here. Maybe we
  -- could go for some other name? Perhaps just Newtype, as that's pretty much
  -- what we wrap in there anyway.
  Cast' :: Coercion -> Value m ws -> Value m ws
  Fun :: (Value m ws -> m (Value m ws)) -> Value m ws
  Ty :: Type -> Value m ws
  Co :: Coercion -> Value m ws

instance KnownWordSize ws => Outputable (Value m ws) where
  ppr = \case
    Primitive prim -> ppr prim
    Data adt@(ADT _ _ val) -> ppr (adtType adt) <+> "=>" <+> text (show val)
    Cast' co val -> ppr co <+> "=>" <+> ppr val
    Fun _ -> text "Fun ??"
    Ty ty -> text "@" <+> ppr ty
    Co co -> ppr co

-- TODO: These errors give very little information on what went actually wrong.
-- I should allow some information to be tagged onto them...
data EvalError where
  IllTyped :: EvalError
  UnsupportedExpr :: EvalError
  UnboundVariable :: EvalError
  deriving Show

instance Outputable EvalError where
  ppr = \case
    IllTyped -> text "ill-typed"
    UnsupportedExpr -> text "unsupported expression"
    UnboundVariable -> text "unbound variable"

-- | Create a cast.
--
-- Merges nested casts. This should always be preferred over manually creating
-- a cast.
mkCast' :: Coercion -> Value m n -> Value m n
mkCast' co = \case
  Cast' co' value -> go (mkTransCo co' co) value mkCast'
  value -> go co value Cast'
  where
    go co' value cont
      | isReflexiveCo co' = value
      | otherwise = cont co' value

-- | Constraints for creating the symbolic values we require.
--
-- These cosntraints are picked such that we can avoid overlapping instances
-- whilst allowing all values we require to be constructed.
type Symbolisable t = (SolvableIdent (ConType t) t, Solvable (ConType t) t, Mergeable t)

-- TODO: I guess this should just return a maybe, as there is only one reason
-- why this would possibly fail.
typedValue
  :: forall m ws
   . MonadError EvalError m
  => KnownWordSize ws
  => (forall t. Symbolisable t => RuntimeValue S t)
  -> Type
  -> m (Value m ws)
typedValue value ty
  | Right prim <- typedPrimitive value ty = pure $ Primitive prim
  | Just (tyCon, tys) <- tcSplitTyConApp_maybe ty
  , Just (ty', co) <- instNewTyCon_maybe tyCon tys = do
    value' <- typedValue value ty'
    let co' = mkSymCo co
    pure $ mkCast' co' value'
  | Just (tyCon, tys) <- tcSplitTyConApp_maybe ty = do
    let adt = mkADT @ws tyCon tys value
    pure $ Data adt
  -- TODO: I think a symbolic function instance would work better here in most
  -- cases.
  | Just (_, _, _, res) <- splitFunTy_maybe ty = do
    let fun _ = typedValue value res
    pure $ Fun fun
  | otherwise = throwError UnsupportedExpr

-- | A value that should not be reachable.
--
-- It will be typed according to the given core type.
invalidValue 
  :: forall m ws
   . MonadError EvalError m
  => KnownWordSize ws
  => Type
  -> m (Value m ws)
invalidValue = typedValue $ mrgThrowError Invalid

-- | Accessor for a field of an ADT.
--
-- The field is a pair of name and its result type.
-- TODO: We should create a Field data structure as they're kind of
-- interconnected. It would make the calls of this function a bit cleaner.
-- TODO: I don't like this as a primed name. We should probably change the name
-- of the normal accessField function.
accessField
  :: forall m ws
   . MonadError EvalError m
  => KnownWordSize ws
  => ADT S
  -> String
  -> Type
  -> m (Value m ws)
accessField adt name = typedValue $ untypedField adt name

-- | Create a function with the arity of whatever we are folding over.
--
-- Use the accumulation function to pass data to the root value of the function.
-- We do it in this way as we cannot just pass values into a Haskell lambda.
nArity
  :: forall m t n a b
   . Monad m
  => Foldable t
  => (b -> m (Value m n))
  -- ^ Root value and what we accumulate.
  -> t a
  -- ^ What we fold over. Decides the arity of the function.
  -> (b -> a -> Value m n -> m b)
  -- ^ Accumulation function
  -> m (b -> m (Value m n))
nArity acc xs f = foldrM' acc xs $ \x acc' -> do
  pure $ \y -> pure . Fun $ \arg -> do
    res <- f y x arg
    acc' res

-- | Apply a function to a value.
--
-- This will fail if the first value is not a function, or if the inner function
-- throws upon receiving the argument.
applyValue
  :: MonadError EvalError m
  => Value m n
  -> Value m n
  -> m (Value m n)
applyValue fun arg = case fun of
  Fun fun' -> fun' arg
  _ -> throwError IllTyped

-- | Apply the given arguments.
--
-- A foldM over a call of 'applyValue'.
applyValues
  :: MonadError EvalError m
  => Value m n
  -> [Value m n]
  -> m (Value m n)
applyValues = foldM applyValue

-- | Compare two values.
--
-- Care must be taken for ADT comparison. We do not check whether the fields of
-- an ADT match the fields of another ADT. Instead, we return an equality of the
-- ADT identifiers. This is a stronger property than just matching fields. Thus,
-- this is only fit as an assumption and not as a final assertion.
-- TODO: I guess this should be like 'strongCmpValue' (as the property we are
-- checking for is strong, i.e. ADT identifier equivalence)
cmpValue
  :: MonadError EvalError m
  => KnownWordSize ws
  => Value m' ws
  -> Value m' ws
  -> m (RuntimeValue S SymBool)
cmpValue = curry $ \case
  (Primitive lhs, Primitive rhs) -> cmpPrimitive lhs rhs
  (Data lhs, Data rhs) -> whyFail IllTyped $ cmpADT lhs rhs
  (Cast' lco lhs, Cast' rco rhs) -> do
    unless (lco `eqCoercion` rco) $ throwError IllTyped
    cmpValue lhs rhs
  (Ty lhs, Ty rhs) -> pure . pure . con $ lhs `eqType` rhs
  (Co lhs, Co rhs) -> pure . pure . con $ lhs `eqCoercion` rhs
  _ -> throwError IllTyped

-- | If then else for symbolic values.
--
-- Note that since types and coercions are not symbolically evaluated, this does
-- not work for these. As Haskell does not have dependent types, this should not
-- be a problem.
iteValue
  :: MonadError EvalError m
  => KnownWordSize ws
  => RuntimeValue S SymBool
  -> Value m ws
  -> Value m ws
  -> m (Value m ws)
iteValue cond = curry $ \case
  (Primitive lhs, Primitive rhs) -> Primitive <$> itePrimitive cond lhs rhs
  (Data lhs, Data rhs) -> do
    let result = iteADT cond lhs rhs
    whyFail IllTyped $ fmap Data result
  (Cast' lco lhs, Cast' rco rhs) -> do
    unless (lco `eqCoercion` rco) $ throwError IllTyped
    result <- iteValue cond lhs rhs
    pure $ Cast' lco result
  (Fun lhs, Fun rhs) -> do
    pure . Fun $ \arg -> do
      lhs' <- lhs arg
      rhs' <- rhs arg
      iteValue cond lhs' rhs'
  -- (Fun _, ADT ty _) -> pprPanic "wow..." $ ppr ty
  -- (lhs, rhs) -> pprPanic ":(" $ ppr lhs <+> "/=" <+> ppr rhs
  _ -> throwError IllTyped

-- | Primitive values supported by the symbolic solver.
data Primitive (ws :: PlatformWordSize) where
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
    Int val -> text "Int# =>" <+> text (show val)
    Int8 val -> text "Int8# =>" <+> text (show val)
    Int16 val -> text "Int16# =>" <+> text (show val)
    Int32 val -> text "Int32# =>" <+> text (show val)
    Int64 val -> text "Int64# =>" <+> text (show val)
    Word val -> text "Word# =>" <+> text (show val)
    Word8 val -> text "Word8# =>" <+> text (show val)
    Word16 val -> text "Word16# =>" <+> text (show val)
    Word32 val -> text "Word32# =>" <+> text (show val)
    Word64 val -> text "Word64# =>" <+> text (show val)
    Float val -> text "Float# =>" <+> text (show val)
    Double val -> text "Double# =>" <+> text (show val)

-- | Construct a primitive, symbolic value with the given type.
typedPrimitive
  :: forall m ws
   . MonadError EvalError m
  => KnownWordSize ws
  => (forall t. Symbolisable t => RuntimeValue S t)
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

-- | Compare primitives values.
cmpPrimitive
  :: MonadError EvalError m
  => KnownWordSize ws
  => Primitive ws
  -> Primitive ws
  -> m (RuntimeValue S SymBool)
cmpPrimitive = curry $ \case
  (Int lhs, Int rhs) -> pure $ cmpRuntime lhs rhs
  (Int8 lhs, Int8 rhs) -> pure $ cmpRuntime lhs rhs
  (Int16 lhs, Int16 rhs) -> pure $ cmpRuntime lhs rhs
  (Int32 lhs, Int32 rhs) -> pure $ cmpRuntime lhs rhs
  (Int64 lhs, Int64 rhs) -> pure $ cmpRuntime lhs rhs
  (Word lhs, Word rhs) -> pure $ cmpRuntime lhs rhs
  (Word8 lhs, Word8 rhs) -> pure $ cmpRuntime lhs rhs
  (Word16 lhs, Word16 rhs) -> pure $ cmpRuntime lhs rhs
  (Word32 lhs, Word32 rhs) -> pure $ cmpRuntime lhs rhs
  (Word64 lhs, Word64 rhs) -> pure $ cmpRuntime lhs rhs
  (Float lhs, Float rhs) -> pure $ cmpRuntime lhs rhs
  (Double lhs, Double rhs) -> pure $ cmpRuntime lhs rhs
  _ -> throwError IllTyped

-- If-then-else for primitive values.
itePrimitive
  :: MonadError EvalError m
  => KnownWordSize ws
  => RuntimeValue S SymBool
  -> Primitive ws
  -> Primitive ws
  -> m (Primitive ws)
itePrimitive cond = curry $ \case
  (Int lhs, Int rhs) -> pure . Int $ iteRuntime cond lhs rhs
  (Int8 lhs, Int8 rhs) -> pure . Int8 $ iteRuntime cond lhs rhs
  (Int16 lhs, Int16 rhs) -> pure . Int16 $ iteRuntime cond lhs rhs
  (Int32 lhs, Int32 rhs) -> pure . Int32 $ iteRuntime cond lhs rhs
  (Int64 lhs, Int64 rhs) -> pure . Int64 $ iteRuntime cond lhs rhs
  (Word lhs, Word rhs) -> pure . Word $ iteRuntime cond lhs rhs
  (Word8 lhs, Word8 rhs) -> pure . Word8 $ iteRuntime cond lhs rhs
  (Word16 lhs, Word16 rhs) -> pure . Word16 $ iteRuntime cond lhs rhs
  (Word32 lhs, Word32 rhs) -> pure . Word32 $ iteRuntime cond lhs rhs
  (Word64 lhs, Word64 rhs) -> pure . Word64 $ iteRuntime cond lhs rhs
  (Float lhs, Float rhs) -> pure . Float $ iteRuntime cond lhs rhs
  (Double lhs, Double rhs) -> pure . Double $ iteRuntime cond lhs rhs
  _ -> throwError IllTyped
