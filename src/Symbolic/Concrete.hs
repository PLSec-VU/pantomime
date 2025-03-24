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

import Prelude hiding ((<>))

import GHC.Plugins
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Tc.Utils.TcType (tcSplitSigmaTy, substTy, eqType)
import GHC.Core.Unify (tcMatchTy)

import Grisette (ToCon (..), EvalSym (..), evalSymToCon)
import Grisette.Unified (EvalModeTag (..))
import Grisette.SymPrim
import Grisette.Internal.SymPrim.Prim.Term (ModelValue (..))

import Control.Monad.Identity (Identity (..))
import Control.Monad.Except (MonadError (..), runExceptT)
import Control.Monad (forM)

import Symbolic.WordSize
import Symbolic.Value
import Symbolic.Runtime
import Symbolic.ADT
import Symbolic.Util

-- TODO: I think this is not the cleanest representation. We should make this
-- a bit better.
data Concrete where
  Record :: DataCon -> [Concrete] -> Concrete
  Value :: ModelValue -> Concrete
  Error :: RuntimeError -> Concrete
  Unknown :: Concrete

-- TODO: This isn't the nicest outputable instance. I think we want a concrete
-- to have a name, such that we can use pprConcrete to output the actual name
-- instead of a bunch of question marks. I additionally would like to emit the
-- type of each argument (and the final output). Ideally in Haskell style:
-- x :: Type
-- x = value
instance Outputable Concrete where
  ppr = pprConcrete ("??? =" <+>) id

pprConcrete
  :: (SDoc -> SDoc)
  -> (SDoc -> SDoc)
  -> Concrete
  -> SDoc
pprConcrete addHeader addParens = \case
  Record dataCon fields
    -- Is saturated tuple?
    | Just sort <- tyConTuple_maybe $ dataConTyCon dataCon
    , length fields == dataConSourceArity dataCon -> do
      let fields' = fsep $ punctuate comma (pprConcrete id id <$> fields)
      addHeader $ tupleParens sort fields'

    -- Is record?
    | labels <- dataConFieldLabels dataCon
    , length labels == dataConSourceArity dataCon -> do
      let header = addHeader $ ppr dataCon

      let prepend pre (name, value) = do
            pprConcrete (pre <+> ppr name <+> equals <+>) id value

      let fields' = vcat $ case zip labels fields of
            -- Add braces on the first and last line. The remaining ones start with
            -- a comma.
            x:xs -> prepend lbrace x : fmap (prepend comma) xs ++ [rbrace]
            -- Skip braces if we don't have fields
            [] -> []

      hang header 2 fields'

    | otherwise -> do
      let header = addHeader $ ppr dataCon
      let fields' = sep $ pprConcrete id parens <$> fields
      addParens $ hang header 2 fields'

  -- TODO: I don't want to print the type here.
  Value value -> addHeader $ text (show value)
  Error err -> addHeader $ "RUNTIME ERROR" <+> ppr err
  Unknown -> addHeader $ text "???"

concretize
  :: forall m m' ws
   . MonadError EvalError m
  => KnownWordSize ws
  => Model
  -> Value m' ws
  -> m Concrete
concretize model = \case
  Primitive prim -> pure $ concretePrimitive model prim
  -- TODO: Clean this horrible piece of code up!
  Data adt -> do
    let stag = accessTag @ws adt
    let ctag = evalSymToCon @(Tag S ws) @(Tag C ws) model stag
    let runRuntime = runIdentity . runExceptT . unRuntimeValue

    case runRuntime $ tagToDataCon ctag of
      Right dataCon -> do
          let (_, _, funTy) = tcSplitSigmaTy $ dataConRepType dataCon
          let (argTys, resTy) = splitFunTys funTy

          -- We try to match the result type of the constructor to the case binder.
          -- Really, this should never fail.
          subst <- whyFail IllTyped $ tcMatchTy resTy (adtType adt)
          let argTys' = substTy subst . scaledThing <$> argTys
          let names = dataConAccessorNames dataCon
          let accessors = zip names argTys'
          fields <- forM accessors $ \(name, ty') -> do
            field <- accessField @m @ws adt name ty'
            concretize model field

          pure $ Record dataCon fields

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
        pure $ Record dataCon [arg']
      go value _ = concretize model value

  -- TODO: There should be a better error to emit than this no? Maybe we
  -- should make a new one... Maybe we should make an error for concrete lookup
  -- failures. Alternatively, I guess we could actually just return the type as
  -- is no? It is actually also a concrete version in a sense.
  Fun _ -> throwError IllTyped
  Ty _ -> throwError IllTyped
  Co _ -> throwError IllTyped

concretePrimitive
  :: forall ws
   . KnownWordSize ws
  => Model
  -> Primitive ws
  -> Concrete
concretePrimitive model = \case
  Int value -> prim @_ @(IntN (WordBits ws)) value
  Int8 value -> prim @_ @IntN8 value
  Int16 value -> prim @_ @IntN16 value
  Int32 value -> prim @_ @IntN32 value
  Int64 value -> prim @_ @IntN64 value
  Word value -> prim @_ @(WordN (WordBits ws)) value
  Word8 value -> prim @_ @WordN8 value
  Word16 value -> prim @_ @WordN16 value
  Word32 value -> prim @_ @WordN32 value
  Word64 value -> prim @_ @WordN64 value
  Float value -> prim @_ @FP32 value
  Double value -> prim @_ @FP64 value
  where
    prim
      :: forall a b
       . ToCon a b
      => EvalSym a
      => SupportedPrim b
      => RuntimeValue S a
      -> Concrete
    prim value = do
      let concrete = evalSymToCon @_ @(RuntimeValue C b) model value
      -- TODO: I think we should either add an instance of ToCon from Runtime to
      -- Either, or we should expose a runRuntime function. This is bad!
      case runIdentity . runExceptT . unRuntimeValue $ concrete of
        Right value' -> Value $ ModelValue value'
        Left err -> Error err
