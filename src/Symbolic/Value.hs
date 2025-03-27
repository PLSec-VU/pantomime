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
  , accessField

  , nArity

  , applyValue
  , applyValues

  , Primitive (..)
  , typedPrimitive
  ) where

import GHC.Plugins hiding (empty)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Builtin.Types.Prim
import GHC.Platform (PlatformWordSize)
import GHC.MonadCore

import Grisette.SymPrim
import Grisette.Unified (EvalModeTag (..))
import Grisette.Lib.Control.Monad.Except (mrgThrowError)
import Grisette
  ( Solvable (..)
  , Mergeable
  , Function (..)
  , Symbol
  , SymbolSetRep (..)
  , indexed
  )

import Control.Monad (foldM, unless)
import Control.Monad.Except (MonadError (..))

import Symbolic.Util
import Symbolic.WordSize
import Symbolic.Runtime
import Symbolic.ADT
import Symbolic.Identifier
import Symbolic.MonadEval
import Grisette.Internal.SymPrim.Prim.Term (SupportedNonFuncPrim)

-- TODO: I feel like we don't really need this. It is literally only passed to
-- the 'applyULam' function.
data ULam mode where
  ULam :: Type -> Type -> RuntimeValue mode (Ident mode) -> ULam mode

-- | Apply an uninterpreted function.
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
applyULam
  :: forall m ws
   . KnownWordSize ws
  => MonadEval m
  => ULam S
  -> Value m ws
  -> m (Value m ws)
applyULam (ULam argTy resTy ident) = \case
  Primitive (Int value) -> do
    guardType intPrimTy

    let untyped :: forall t. Interpretable (SymIntN (WordBits ws) -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> SymIntN (WordBits ws) -~> t
          liftApply apply ident value

    typedValue untyped resTy

  Primitive (Int8 value) -> do
    guardType int8PrimTy

    let untyped :: forall t. Interpretable (SymIntN8 -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> SymIntN8 -~> t
          liftApply apply ident value

    typedValue untyped resTy

  Primitive (Int16 value) -> do
    guardType int16PrimTy

    let untyped :: forall t. Interpretable (SymIntN16 -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> SymIntN16 -~> t
          liftApply apply ident value

    typedValue untyped resTy

  Primitive (Int32 value) -> do
    guardType int32PrimTy

    let untyped :: forall t. Interpretable (SymIntN32 -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> SymIntN32 -~> t
          liftApply apply ident value

    typedValue untyped resTy

  Primitive (Int64 value) -> do
    guardType int64PrimTy

    let untyped :: forall t. Interpretable (SymIntN64 -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> SymIntN64 -~> t
          liftApply apply ident value

    typedValue untyped resTy

  Primitive (Word value) -> do
    guardType intPrimTy

    let untyped :: forall t. Interpretable (SymWordN (WordBits ws) -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> SymWordN (WordBits ws) -~> t
          liftApply apply ident value

    typedValue untyped resTy

  Primitive (Word8 value) -> do
    guardType word8PrimTy

    let untyped :: forall t. Interpretable (SymWordN8 -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> SymWordN8 -~> t
          liftApply apply ident value

    typedValue untyped resTy

  Primitive (Word16 value) -> do
    guardType word16PrimTy

    let untyped :: forall t. Interpretable (SymWordN16 -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> SymWordN16 -~> t
          liftApply apply ident value

    typedValue untyped resTy

  Primitive (Word32 value) -> do
    guardType word32PrimTy

    let untyped :: forall t. Interpretable (SymWordN32 -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> SymWordN32 -~> t
          liftApply apply ident value

    typedValue untyped resTy

  Primitive (Word64 value) -> do
    guardType word64PrimTy

    let untyped :: forall t. Interpretable (SymWordN64 -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> SymWordN64 -~> t
          liftApply apply ident value

    typedValue untyped resTy

  Primitive (Float value) -> do
    guardType floatPrimTy

    let untyped :: forall t. Interpretable (SymFP32 -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> SymFP32 -~> t
          liftApply apply ident value

    typedValue untyped resTy

  Primitive (Double value) -> do
    guardType doublePrimTy

    let untyped :: forall t. Interpretable (SymFP64 -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> SymFP64 -~> t
          liftApply apply ident value

    typedValue untyped resTy

  Data adt@(ADT _ _ ident') -> do
    guardType $ adtType adt

    let untyped :: forall t. Interpretable (Ident S -~> t) => RuntimeValue S t
        untyped = do
          let apply = sym name :: Ident S -~> Ident S -~> t
          liftApply apply ident ident'

    typedValue untyped resTy

  Cast' co value -> do
    guardType $ coercionRKind co
    let innerTy = coercionLKind co
    applyULam (ULam innerTy resTy ident) value

  -- TODO: Implement this!
  -- FIXME: Should we substitute a type variable into the result type? I think
  -- we really should!!!
  Fun innerArgTy fun -> do
    -- FIXME: This check doesn't make sense. We want to ensure that the entire
    -- function has the same type as the ULam argument. Or at the very least,
    -- that the ULam expects a function whose type matches that of the given
    -- Fun.
    -- Ensure that the given value argument (which is itself a function) matches
    -- the expected argument of the function. Since a value Fun only carries its
    -- input type, we just check whether this matches.
    (_, _, innerArgTy', _) <- whyFail IllTyped $ splitFunTy_maybe argTy
    unless (innerArgTy `eqType` innerArgTy') $ throwError IllTyped

    arg <- freshValue @m @ws argTy
    _assumption <- evalEq (Fun innerArgTy fun) arg
    -- TODO: This should create a typed value for the argument. Then do an
    -- equivalence assumption where the arg should be equal to the fun. After
    -- we should compose the symbolic function application with the identifier
    -- for the function.
    --
    -- Now I'm unsure what exactly to return here. I would like to apply the
    -- identifier in 'arg' to form something of the following form:
    --
    -- let untyped :: forall t. Interpretable (Ident S -~> t) => RuntimeValue S t
    --     untyped = do
    --       let apply = sym name :: Ident S -~> Ident S -~> t
    --       liftApply apply ident funIdent

    -- typedValue untyped resTy
    --
    -- But how do I get the funIdent. It should somehow be extracted from the
    -- 'arg' no?

    throwError UnsupportedExpr

  _ -> throwError UnsupportedExpr
  where
    liftApply apply = liftA2 $ \a0 a1 -> apply # a0 # a1
    guardType ty = unless (ty `eqType` argTy) $ throwError IllTyped
    -- TODO: I think we should make a separate file/spot with all the
    -- non-indexed names. It is very messy and error prone to define global
    -- names all over the place.
    name = "!apply"

-- TODO: Could we adjust n to be a DataKind of the actual word size data type
-- from GHC? To me that seems a lot cleaner, as it represents more
-- accurately what values n should range over are exactly.
data Value m ws where
  Primitive :: Primitive ws -> Value m ws
  Data :: ADT S -> Value m ws
  -- TODO: I don't really like the prime on the name of Cast here. Maybe we
  -- could go for some other name? Perhaps just Newtype, as that's pretty much
  -- what we wrap in there anyway.
  Cast' :: Coercion -> Value m ws -> Value m ws
  Fun :: Kind  -> (Value m ws -> m (Value m ws)) -> Value m ws
  Ty :: Type -> Value m ws
  Co :: Coercion -> Value m ws

instance KnownWordSize ws => Outputable (Value m ws) where
  ppr = \case
    Primitive prim -> ppr prim
    Data adt@(ADT _ _ val) -> ppr (adtType adt) <+> "=>" <+> text (show val)
    Cast' co val -> ppr co <+> "=>" <+> ppr val
    Fun argTy _ -> ppr argTy <+> "-> ? => ?"
    Ty ty -> text "@" <+> ppr ty
    Co co -> ppr co

instance (MonadEval m, KnownWordSize ws) => EvalEq m (Value m ws) where
  -- Compare two values.
  --
  -- Care must be taken for ADT comparison. We do not check whether the fields of
  -- an ADT match the fields of another ADT. Instead, we return an equality of the
  -- ADT identifiers. This is a stronger property than just matching fields. Thus,
  -- this is only fit as an assumption and not as a final assertion.
  -- TODO: I guess this should be like 'strongCmpValue' (as the property we are
  -- checking for is strong, i.e. ADT identifier equivalence)
  evalEq = curry $ \case
    (Primitive lhs, Primitive rhs) -> evalEq lhs rhs
    (Data lhs, Data rhs) -> evalEq lhs rhs
    (Cast' lco lhs, Cast' rco rhs) -> do
      unless (lco `eqCoercion` rco) $ throwError IllTyped
      evalEq lhs rhs

    (Fun lty lhs, Fun rty rhs) -> do
      -- TODO: This thing is very messy!
      unless (lty `eqType` rty) $ throwError IllTyped
      idx <- freshIdx
      let symbol = indexed "!qarg" idx
      let untyped :: forall t. Solvable (ConType t) t => RuntimeValue S t
          untyped = pure $ sym symbol
      arg <- typedValue untyped lty

      lhs' <- lhs arg
      rhs' <- rhs arg
      eq <- evalEq lhs' rhs'

      typed <- valueSymbol @m @ws symbol lty
      let quantifier = buildSymbolSet typed
      dbg' $ show quantifier
      -- FIXME: The quantifier is escaping its definition. This is because the
      -- quantifier is used in the guard, but the forall only applies to the
      -- Right branch. It appears that leaking underconstraints the output.
      -- How would I quantify the entire union? I'm not sure this is possible...
      -- I'll have to think what the meaning is even of the quantification.
      pure $ forallSet quantifier <$> eq

    (Ty lhs, Ty rhs) -> pure . pure . con $ lhs `eqType` rhs
    (Co lhs, Co rhs) -> pure . pure . con $ lhs `eqCoercion` rhs
    _ -> throwError IllTyped

instance (MonadEval m, KnownWordSize ws) => EvalIte m (Value m ws) where
  evalIte cond = curry $ \case
    (Primitive lhs, Primitive rhs) -> Primitive <$> evalIte cond lhs rhs
    (Data lhs, Data rhs) -> Data <$> evalIte cond lhs rhs
    (Cast' lco lhs, Cast' rco rhs) -> do
      unless (lco `eqCoercion` rco) $ throwError IllTyped
      result <- evalIte cond lhs rhs
      pure $ Cast' lco result
    (Fun larg lhs, Fun rarg rhs) -> do
      unless (larg `eqType` rarg) $ throwError IllTyped
      pure . Fun larg $ \arg -> do
        lhs' <- lhs arg
        rhs' <- rhs arg
        evalIte cond lhs' rhs'
    (Ty _, Ty _) -> throwError UnsupportedExpr
    (Co _, Co _) -> throwError UnsupportedExpr
    _ -> throwError IllTyped

instance (MonadEval m, KnownWordSize ws) => EvalAssume (Value m ws) where
  evalAssume cond = \case
    Primitive prim -> Primitive $ evalAssume cond prim
    Data adt -> Data $ evalAssume cond adt
    Cast' co val -> Cast' co $ evalAssume cond val
    Fun argTy fun -> do
      Fun argTy $ \arg -> do
        evalAssume cond <$> fun arg
    -- TODO: I guess there is nothing to assume in these cases. Still this seems
    -- like it could introduce some unexpected behaviour if we're not careful.
    -- I think we should change this. We shouldn't just drop assumptions...
    Ty ty -> Ty ty
    Co co -> Co co

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
-- These constraints are picked such that we can avoid overlapping instances
-- whilst allowing all values we require to be constructed.
-- TODO: This once required Hashable as an exposed package. We should remove it
-- from the package list, as we do not use it.
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
typedValue
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => (forall t. Symbolisable t ws => RuntimeValue S t)
  -> Type
  -> m (Value m ws)
typedValue value ty
  | Right prim <- typedPrimitive value ty = pure $ Primitive prim
  | Just (tyCon, tys) <- tcSplitTyConApp_maybe ty
  , Just (_, co) <- instNewTyCon_maybe tyCon tys = do
    value' <- typedValue value ty
    let co' = mkSymCo co
    pure $ mkCast' co' value'
  | Just (tyCon, tys) <- tcSplitTyConApp_maybe ty
  , isDataTyCon tyCon = do
    let adt = mkADT @ws tyCon tys value
    pure $ Data adt
  -- TODO: I think a symbolic function instance would work better here in most
  -- cases.
  | Just (_, _, argTy, resTy) <- splitFunTy_maybe ty = do

    -- idx <- freshIdx
    -- let symbol = indexed "!FUN" idx
    -- let ident = pure $ sym symbol

    -- TODO: Clean this stuff up!
    let x = ULam @S argTy resTy value

    -- let fun = Fun argTy $ applyULam x
    -- eq <- evalEq ident value
    -- dbg' $ show eq
    -- pure $ evalAssume eq fun
    pure . Fun argTy $ applyULam x

    -- FIXME: This function type really doesn't make sense. We are ignoring the
    -- argument here. We should use the ULam type we created to make an
    -- uninterpreted function here!
    --
    -- The next step would be to implement a the comparison between this
    -- symbolic version and an actual implementation. Perhaps, we could do it
    -- in two steps. First, the ULam should be wrapped inside of a Fun always.
    -- Then we only need to implement the compare between two Fun types. The
    -- comparison would need to saturate the functions and then check the
    -- output. This would mean that ULam will actually not be a part of Value
    -- btw.
    -- pure $ Fun argTy fun
  | otherwise = throwError UnsupportedExpr

valueSymbol
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => Symbol
  -> Type
  -> m SomeTypedConstantSymbol
valueSymbol symbol ty
  | Right prim <- primitiveSymbol @_ @ws symbol ty = pure prim
  | Just (tyCon, tys) <- tcSplitTyConApp_maybe ty
  , Just (_, co) <- instNewTyCon_maybe tyCon tys = do
    let ty' = coercionRKind co
    valueSymbol @m @ws symbol ty'
  | Just (tyCon, _) <- tcSplitTyConApp_maybe ty
  , isDataTyCon tyCon = symbol' @(Ident C)
  -- cases.
  | Just (_, _, _, _) <- splitFunTy_maybe ty = symbol' @(Ident C)
  | otherwise = throwError UnsupportedExpr
  where
    symbol' :: forall t. SupportedNonFuncPrim t => m SomeTypedConstantSymbol
    symbol' = pure $ SomeTypedSymbol (typedConstantSymbol @t symbol)

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

-- | Accessor for a field of an ADT.
--
-- The field is a pair of name and its result type.
-- TODO: We should create a Field data structure as they're kind of
-- interconnected. It would make the calls of this function a bit cleaner.
accessField
  :: forall m ws
   . MonadEval m
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
  -> t (a, Kind)
  -- ^ What we fold over. Decides the arity of the function.
  -> (b -> a -> Value m n -> m b)
  -- ^ Accumulation function
  -> m (b -> m (Value m n))
nArity acc xs f = foldrM' acc xs $ \(x, argTy) acc' -> do
  pure $ \y -> pure . Fun argTy $ \arg -> do
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
  Fun _ fun' -> fun' arg
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
    Int val -> text "Int# =>" <+> pprRuntime val
    Int8 val -> text "Int8# =>" <+> pprRuntime val
    Int16 val -> text "Int16# =>" <+> pprRuntime val
    Int32 val -> text "Int32# =>" <+> pprRuntime val
    Int64 val -> text "Int64# =>" <+> pprRuntime val
    Word val -> text "Word# =>" <+> pprRuntime val
    Word8 val -> text "Word8# =>" <+> pprRuntime val
    Word16 val -> text "Word16# =>" <+> pprRuntime val
    Word32 val -> text "Word32# =>" <+> pprRuntime val
    Word64 val -> text "Word64# =>" <+> pprRuntime val
    Float val -> text "Float# =>" <+> pprRuntime val
    Double val -> text "Double# =>" <+> pprRuntime val
    where
      -- pprRuntime :: PPrint a => RuntimeValue S a -> SDoc
      -- pprRuntime = text . show . pformatText . unRuntimeValue
      pprRuntime :: Show a => RuntimeValue S a -> SDoc
      pprRuntime = text . show 

instance (MonadEval m, KnownWordSize ws) => EvalEq m (Primitive ws) where
  evalEq = curry $ \case
    (Int lhs, Int rhs) -> evalEq lhs rhs
    (Int8 lhs, Int8 rhs) -> evalEq lhs rhs
    (Int16 lhs, Int16 rhs) -> evalEq lhs rhs
    (Int32 lhs, Int32 rhs) -> evalEq lhs rhs
    (Int64 lhs, Int64 rhs) -> evalEq lhs rhs
    (Word lhs, Word rhs) -> evalEq lhs rhs
    (Word8 lhs, Word8 rhs) -> evalEq lhs rhs
    (Word16 lhs, Word16 rhs) -> evalEq lhs rhs
    (Word32 lhs, Word32 rhs) -> evalEq lhs rhs
    (Word64 lhs, Word64 rhs) -> evalEq lhs rhs
    (Float lhs, Float rhs) -> evalEq lhs rhs
    (Double lhs, Double rhs) -> evalEq lhs rhs
    _ -> throwError IllTyped

instance (MonadEval m, KnownWordSize ws) => EvalIte m (Primitive ws) where
  evalIte cond = curry $ \case
    (Int lhs, Int rhs) -> Int <$> evalIte cond lhs rhs
    (Int8 lhs, Int8 rhs) -> Int8 <$> evalIte cond lhs rhs
    (Int16 lhs, Int16 rhs) -> Int16 <$> evalIte cond lhs rhs
    (Int32 lhs, Int32 rhs) -> Int32 <$> evalIte cond lhs rhs
    (Int64 lhs, Int64 rhs) -> Int64 <$> evalIte cond lhs rhs
    (Word lhs, Word rhs) -> Word <$> evalIte cond lhs rhs
    (Word8 lhs, Word8 rhs) -> Word8 <$> evalIte cond lhs rhs
    (Word16 lhs, Word16 rhs) -> Word16 <$> evalIte cond lhs rhs
    (Word32 lhs, Word32 rhs) -> Word32 <$> evalIte cond lhs rhs
    (Word64 lhs, Word64 rhs) -> Word64 <$> evalIte cond lhs rhs
    (Float lhs, Float rhs) -> Float <$> evalIte cond lhs rhs
    (Double lhs, Double rhs) -> Double <$> evalIte cond lhs rhs
    _ -> throwError IllTyped

instance KnownWordSize ws => EvalAssume (Primitive ws) where
  evalAssume cond = \case
    Int value -> Int $ evalAssume cond value
    Int8 value -> Int8 $ evalAssume cond value
    Int16 value -> Int16 $ evalAssume cond value
    Int32 value -> Int32 $ evalAssume cond value
    Int64 value -> Int64 $ evalAssume cond value
    Word value -> Word $ evalAssume cond value
    Word8 value -> Word8 $ evalAssume cond value
    Word16 value -> Word16 $ evalAssume cond value
    Word32 value -> Word32 $ evalAssume cond value
    Word64 value -> Word64 $ evalAssume cond value
    Float value -> Float $ evalAssume cond value
    Double value -> Double $ evalAssume cond value

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

primitiveSymbol
  :: forall m ws
   . MonadError EvalError m
  => KnownWordSize ws
  => Symbol
  -> Type
  -> m SomeTypedConstantSymbol
primitiveSymbol symbol ty
  | ty `eqType` intPrimTy = symbol' @(IntN (WordBits ws))
  | ty `eqType` int8PrimTy = symbol' @IntN8
  | ty `eqType` int16PrimTy = symbol' @IntN16
  | ty `eqType` int32PrimTy = symbol' @IntN32
  | ty `eqType` int64PrimTy = symbol' @IntN64
  | ty `eqType` wordPrimTy = symbol' @(WordN (WordBits ws))
  | ty `eqType` word8PrimTy = symbol' @WordN8
  | ty `eqType` word16PrimTy = symbol' @WordN16
  | ty `eqType` word32PrimTy = symbol' @WordN32
  | ty `eqType` word64PrimTy = symbol' @WordN64
  | ty `eqType` floatPrimTy = symbol' @FP32
  | ty `eqType` doublePrimTy = symbol' @FP64
  | otherwise = throwError UnsupportedExpr
  where
    symbol' :: forall t. SupportedNonFuncPrim t => m SomeTypedConstantSymbol
    symbol' = pure $ SomeTypedSymbol (typedConstantSymbol @t symbol)
