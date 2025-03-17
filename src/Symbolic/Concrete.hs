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

module Symbolic.Concrete
  ( Concrete (..)
  , concretize
  ) where

import GHC.Plugins

import Grisette (ToCon (..), EvalSym (..))
import Grisette.SymPrim
import Grisette.Internal.SymPrim.Prim.Term (ModelValue (..))

import Control.Monad.Except (MonadError (..))

import Data.Functor ((<&>))

import Symbolic.KnownPos
import Symbolic.Value
import Symbolic.Runtime
import Symbolic.ADT
import Grisette.Core (evalSymToCon)
import GHC.Tc.Utils.TcType (tcSplitSigmaTy, substTy, eqType)
import GHC.Core.Unify (tcMatchTy)
import Symbolic.Util
import GHC.Core.TyCo.Rep (scaledThing)
import Control.Monad (forM)

-- TODO: I think this is not the cleanest representation. We should make this
-- a bit better.
data Concrete where
  Record :: DataCon -> [(String, Concrete)] -> Concrete
  Primitive :: ModelValue -> Concrete
  Error :: RuntimeError -> Concrete
  Unknown :: Concrete

-- TODO: The indentation is a bit off because we vertically nest only the
-- DataCon, while we should nest it with the assignment 'value = DataCon'.
instance Outputable Concrete where
  ppr = \case
    Record dataCon fields -> ppr dataCon $+$ (nest 2 . braces' . vcat $ fields')
      where
        braces' x = lbrace <+> x $+$ rbrace
        fields' = punctuate (text ", ") $ fields <&> pair
        pair (name, value) = text name <+> "=" <+> ppr value
    Primitive value -> text $ show value
    Error err -> "error value: " <+> ppr err
    Unknown -> text "???"

concretize
  :: forall m m' n
   . MonadError SymbolicError m
  => KnownPos n
  => Model
  -> Value m' n
  -> m Concrete
concretize model = \case
  Int value -> prim @_ @(IntN n) value
  Int8 value -> prim @_ @IntN8 value
  Int16 value -> prim @_ @IntN16 value
  Int32 value -> prim @_ @IntN32 value
  Int64 value -> prim @_ @IntN64 value
  Word value -> prim @_ @(WordN n) value
  Word8 value -> prim @_ @WordN8 value
  Word16 value -> prim @_ @WordN16 value
  Word32 value -> prim @_ @WordN32 value
  Word64 value -> prim @_ @WordN64 value
  Float value -> prim @_ @FP32 value
  Double value -> prim @_ @FP64 value
  -- TODO: Clean this horrible piece of code up!
  ADT ty adt -> case evalSymToCon @_ @(Either RuntimeError (Tag n)) model $ accessTag @n adt of
    Right tag -> do
      case tagToDataCon tag ty of
        Just dataCon -> do
          let (_, _, funTy) = tcSplitSigmaTy $ dataConRepType dataCon
          let (argTys, resTy) = splitFunTys funTy

          -- We try to match the result type of the constructor to the case binder.
          -- Really, this should never fail.
          subst <- whyFail IllTyped $ tcMatchTy resTy ty
          let argTys' = substTy subst . scaledThing <$> argTys
          let names = dataConAccessorNames dataCon
          let accessors = zip names argTys'
          fields <- forM accessors $ \(name, ty') -> do
            field <- accessField' @m @n adt name ty'
            concretize model field

          pure $ Record dataCon (zip names fields)
        Nothing -> pure Unknown

    Left err -> pure $ Error err

  -- TODO: Clean this horrible piece of code up!
  Cast' co value' -> go value' $ coercionRKind co
    where
      go value ty | not $ ty `eqType` coercionLKind co = do
        (tyCon, tys) <- whyFail IllTyped $ splitTyConApp_maybe ty
        dataCon <- whyFail undefined $ tyConSingleDataCon_maybe tyCon
        argTy <- case dataConInstArgTys dataCon tys of
          [argTy] -> pure $ scaledThing argTy
          _ -> throwError IllTyped
        arg' <- go value argTy
        pure $ Record dataCon [("0", arg')]
      go value _ = concretize model value

  -- TODO: There should be a better error to emit than this no? Maybe we
  -- should make a new one... Maybe we should make an error for concrete lookup
  -- failures. Alternatively, I guess we could actually just return the type as
  -- is no? It is actually also a concrete version in a sense.
  Fun _ -> throwError IllTyped
  Ty _ -> throwError IllTyped
  Co _ -> throwError IllTyped
  where
    prim
      :: forall a b
       . ToCon a b
      => EvalSym a
      => SupportedPrim b
      => RuntimeValue a
      -> m Concrete
    prim value = do
      let concrete = evalSymToCon @_ @(Either RuntimeError b) model value
      case concrete of
        Right value' -> pure $ Primitive (ModelValue value')
        Left err -> pure $ Error err
