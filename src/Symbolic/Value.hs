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
  , accessField'
  , typedValue
  , invalidValue
  , nArity

  , applyValue
  , applyValues
  , cmpValue
  , iteValue
  ) where

import GHC.Plugins hiding (empty)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Builtin.Types.Prim

import Grisette.SymPrim
import Grisette (Solvable (..))

import Control.Monad (unless, foldM)
import Control.Monad.Except (MonadError (..))

import Symbolic.Util
import Symbolic.KnownPos
import Symbolic.Runtime
import Symbolic.ADT

-- TODO: I think the Int and Word stuff should go under one constructor: Prim.
-- They all function pretty much the same anyway.
data Value m n where
  -- TODO: Add support for Char
  -- TODO: Add support for ByteArray (as this is how big integers are
  -- TODO: Add support for symbolic (higher order) functions.
  -- implemented under the hood).
  -- Char :: RuntimeValue (SymWordN 31) -> Value m n
  -- BigNat :: RuntimeValue SymInteger -> Value m n
  Int :: RuntimeValue (SymIntN n) -> Value m n
  Int8 :: RuntimeValue SymIntN8 -> Value m n
  Int16 :: RuntimeValue SymIntN16 -> Value m n
  Int32 :: RuntimeValue SymIntN32 -> Value m n
  Int64 :: RuntimeValue SymIntN64 -> Value m n
  Word :: RuntimeValue (SymWordN n) -> Value m n
  Word8 :: RuntimeValue SymWordN8 -> Value m n
  Word16 :: RuntimeValue SymWordN16 -> Value m n
  Word32 :: RuntimeValue SymWordN32 -> Value m n
  Word64 :: RuntimeValue SymWordN64 -> Value m n
  Float :: RuntimeValue SymFP32 -> Value m n
  Double :: RuntimeValue SymFP64 -> Value m n
  ADT :: Type -> RuntimeValue SymADT -> Value m n
  -- TODO: I don't really like the prime on the name of Cast here. Maybe we
  -- could go for some other name? Perhaps just Newtype, as that's pretty much
  -- what we wrap in there anyway.
  Cast' :: Coercion -> Value m n -> Value m n
  Fun :: (Value m n -> m (Value m n)) -> Value m n
  Ty :: Type -> Value m n
  Co :: Coercion -> Value m n

instance KnownPos n => Outputable (Value m n) where
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
    ADT ty val -> ppr ty <+> "=>" <+> text (show val)
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

-- TODO: I guess this should just return a maybe, as there is only one reason
-- why this would possibly fail.
typedValue
  :: forall m n
   . MonadError EvalError m
  => KnownPos n
  => (forall c t. Solvable c t => LinkedRep c t => RuntimeValue t)
  -> Type
  -> m (Value m n)
typedValue value ty
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
  | Just (tyCon, tys) <- tcSplitTyConApp_maybe ty
  , Just (ty', co) <- instNewTyCon_maybe tyCon tys = do
    value' <- typedValue value ty'
    let co' = mkSymCo co
    pure $ mkCast' co' value'
  | Just _ <- tcSplitTyConApp_maybe ty = pure $ ADT ty value
  | Just (_, _, _, res) <- splitFunTy_maybe ty = do
    let fun _ = typedValue value res
    pure $ Fun fun
  | otherwise = throwError UnsupportedExpr

-- | A value that should not be reachable.
--
-- It will be typed according to the given core type.
invalidValue 
  :: forall m n
   . MonadError EvalError m
  => KnownPos n
  => Type
  -> m (Value m n)
invalidValue = typedValue $ throwError Invalid

-- | Accessor for a field of an ADT.
--
-- The field is a pair of name and its result type.
-- TODO: We should create a Field data structure as they're kind of
-- interconnected. It would make the calls of this function a bit cleaner.
-- TODO: I don't like this as a primed name. We should probably change the name
-- of the normal accessField function.
accessField'
  :: forall m n
   . MonadError EvalError m
  => KnownPos n
  => RuntimeValue SymADT
  -> String
  -> Type
  -> m (Value m n)
accessField' adt name ty
  -- TODO: Why can we not pass 'construct' to 'typedValue'? I don't understand
  -- why it has overlapping instances... For now, we just duplicate some code...
  | ty `eqType` intPrimTy = pure $ Int construct
  | ty `eqType` int8PrimTy = pure $ Int8 construct
  | ty `eqType` int16PrimTy = pure $ Int16 construct
  | ty `eqType` int32PrimTy = pure $ Int32 construct
  | ty `eqType` int64PrimTy = pure $ Int64 construct
  | ty `eqType` wordPrimTy = pure $ Word construct
  | ty `eqType` word8PrimTy = pure $ Word8 construct
  | ty `eqType` word16PrimTy = pure $ Word16 construct
  | ty `eqType` word32PrimTy = pure $ Word32 construct
  | ty `eqType` word64PrimTy = pure $ Word64 construct
  | ty `eqType` floatPrimTy = pure $ Float construct
  | ty `eqType` doublePrimTy = pure $ Double construct
  | Just (tyCon, tys) <- tcSplitTyConApp_maybe ty
  , Just (ty', co) <- instNewTyCon_maybe tyCon tys = do
    value <- accessField' adt name ty'
    let co' = mkSymCo co
    pure $ mkCast' co' value
  | Just _ <- tcSplitTyConApp_maybe ty = pure $ ADT ty construct
  | otherwise = throwError UnsupportedExpr
  where
    construct
      :: forall c t
       . LinkedRep (ADT --> c) (SymADT -~> t)
      => LinkedRep c t
      => RuntimeValue t
    construct = accessField adt name

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
  => KnownPos n
  => Value m' n
  -> Value m' n
  -> m (RuntimeValue SymBool)
cmpValue = curry $ \case
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
  (ADT lty lhs, ADT rty rhs) -> do
    unless (lty `eqType` rty) $ throwError $ IllTyped
    pure $ cmpRuntime lhs rhs
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
  => KnownPos n
  => RuntimeValue SymBool
  -> Value m n
  -> Value m n
  -> m (Value m n)
iteValue cond = curry $ \case
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
  (ADT lty lhs, ADT rty rhs) -> do
    unless (lty `eqType` rty) $ throwError IllTyped
    pure . ADT lty $ iteRuntime cond lhs rhs
  (Cast' lco lhs, Cast' rco rhs) -> do
    unless (lco `eqCoercion` rco) $ throwError IllTyped
    result <- iteValue cond lhs rhs
    pure $ Cast' lco result
  (Fun lhs, Fun rhs) -> do
    pure . Fun $ \arg -> do
      lhs' <- lhs arg
      rhs' <- rhs arg
      iteValue cond lhs' rhs'
  _ -> throwError IllTyped
