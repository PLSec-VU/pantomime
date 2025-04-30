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

module Symbolic.Concrete
  ( Concrete (..)
  , concretise
  ) where

import Prelude hiding ((<>))

import GHC.Plugins
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Tc.Utils.TcType (eqType)
import GHC.TypeLits (SomeNat(..), someNatVal)

import Grisette (ToCon (..), EvalSym (..), evalSymToCon, indexed, Symbol)
import Grisette.Unified (EvalModeTag (..))
import Grisette.SymPrim

import Control.Monad.Except (MonadError (..))
import Control.Monad (forM)

import Data.Typeable (cast)

import Symbolic.WordSize
import Symbolic.Value
import Symbolic.Runtime
import Symbolic.Util
import Symbolic.Evaluate
import Symbolic.MonadEval
import Symbolic.Dict
import Symbolic.Sized.BitVector

-- TODO: I think this is not the cleanest representation. We should make this
-- a bit better.
data Concrete where
  Record :: DataCon -> [Concrete] -> Concrete
  Function :: Symbol -> Type -> Concrete -> Concrete
  Value :: Show a => a -> Concrete
  Error :: RuntimeError -> Concrete
  Unknown :: Concrete

-- TODO: This isn't the nicest outputable instance. I think we want a concrete
-- to have a name, such that we can use pprConcrete to output the actual name
-- instead of a bunch of question marks. I additionally would like to emit the
-- type of each argument (and the final output). Ideally in Haskell style:
-- x :: Type
-- x = value
instance Outputable Concrete where
  ppr = pprConcrete ("? =" <+>) id

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

  expr@(Function _ _ _) -> do
    let pprFun name ty = parens $ text (show name) <+> "::" <+> ppr ty

    let collectFuns (Function name ty inner) = do
          let (bndrs, body) = collectFuns inner
          ((name, ty):bndrs, body)
        collectFuns body = ([], body)

    let (bndrs, body) = collectFuns expr

    let args = sep $ uncurry pprFun <$> bndrs
    let header = addHeader $ "\\" <+> args <+> arrow

    let body' = pprConcrete id id body
    addParens $ hang header 2 body'

  Value value -> addHeader $ text (show value)
  Error err -> addHeader $ "RUNTIME ERROR" <+> ppr err
  Unknown -> addHeader $ "undefined"

-- TODO: I should be able to reconstruct a full CoreExpr from a Value. That
-- would be the ideal concrete form!
concretise
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => Model
  -> Value m ws
  -> m Concrete
concretise model = \case
  Primitive prim -> pure $ concretePrimitive model prim
  -- TODO: Clean this horrible piece of code up!
  Data adt -> do
    let tag = evalSymToCon @_ @(Tag C ws) model $ adtTag adt

    -- dbg' . show $ adtTag adt
    case unRuntimeC tag of
      Right tag'
        | Just dataCon <- tagToDataCon tag' $ adtTyCon adt
        , Just fields <- adtDataConFields adt dataCon -> do
          fields' <- forM fields $ concretise model
          pure $ Record dataCon fields'
        
      -- TODO: This shouldn't happen!
      Right _ -> pure Unknown
      Left Invalid -> pure Unknown
      Left err -> pure $ Error err

  -- TODO: Clean this horrible piece of code up!
  Cast' co value' -> go value' $ coercionRKind co
    where
      go value ty | not $ ty `eqType` coercionLKind co = do
        (tyCon, tys) <- whyFail IllTyped $ splitTyConApp_maybe ty
        dataCon <- whyFail IllTyped $ tyConSingleDataCon_maybe tyCon
        argTy <- case dataConInstArgTys dataCon tys of
          [argTy] -> pure $ scaledThing argTy
          _ -> throwError IllTyped
        arg' <- go value argTy
        pure $ Record dataCon [arg']
      go value _ = concretise model value

  Fun argTy _ -> do
    idx <- freshIdx
    let symbol = indexed "arg" idx
    -- TODO: We should actually create a concrete body. It's not very trivial
    -- though, as fetching the concrete instance of function accessors and such
    -- is completely bogus as output. Ideally, we just reconstruct a CoreExpr.
    -- let untyped :: forall t. Solvable (ConType t) t => RuntimeValue S t
        -- untyped = pure $ sym symbol

    -- arg <- typedValue @m @ws untyped argTy
    -- res <- fun arg

    -- body <- concretise model res
    let body = Unknown
    pure $ Function symbol argTy body

  Poly _ty _ident -> pure $ Unknown

  -- TODO: This is super ugly!
  Opaque' ty value
    -- TODO Actually check the TyCon!
    | Just (_tyCon, [size]) <- tcSplitTyConApp_maybe ty
    , Just (SomeNat @n _) <- normNumLitTy size >>= someNatVal
    , Just Dict <- posNat @n
    , Just bv <- cast @_ @(RuntimeValue S (WordN' S n)) value
    -> pure $ primCon model bv

  Opaque' ty value
    -- TODO Actually check the TyCon!
    | Just (_tyCon, [size]) <- tcSplitTyConApp_maybe ty
    , Just (SomeNat @n _) <- normNumLitTy size >>= someNatVal
    , Just Dict <- posNat @n
    , Just bv <- cast @_ @(RuntimeValue S (IntN' S n)) value
    -> pure $ primCon model bv

  Opaque' ty value
    -- TODO Actually check the TyCon!
    | Just (_tyCon, []) <- tcSplitTyConApp_maybe ty
    , Just bv <- cast @_ @(RuntimeValue S (WordN' S 1)) value
    -> pure $ primCon model bv

  Opaque' _ty _value -> pure $ Unknown

  -- TODO: There should be a better error to emit than this no? Maybe we
  -- should make a new one... Maybe we should make an error for concrete lookup
  -- failures. Alternatively, I guess we could actually just return the type as
  -- is no? It is actually also a concrete version in a sense.
  Ty _ -> throwError IllTyped
  Co _ -> throwError IllTyped

concretePrimitive
  :: forall ws
   . KnownWordSize ws
  => Model
  -> Primitive ws
  -> Concrete
concretePrimitive model = \case
  Int value -> prim' value
  Int8 value -> prim' value
  Int16 value -> prim' value
  Int32 value -> prim' value
  Int64 value -> prim' value
  Word value -> prim' value
  Word8 value -> prim' value
  Word16 value -> prim' value
  Word32 value -> prim' value
  Word64 value -> prim' value
  Float value -> prim' value
  Double value -> prim' value
  ByteArray _ value -> prim' value
  where
    prim'
      :: forall a
       . ToCon a (ConType a)
      => EvalSym a
      => Show (ConType a)
      => RuntimeValue S a
      -> Concrete
    prim' = primCon model

-- TODO: Maybe give this a better name? This function is also kind of ugly...
primCon
  :: forall a
   . ToCon a (ConType a)
  => EvalSym a
  => Show (ConType a)
  => Model
  -> RuntimeValue S a
  -> Concrete
primCon model value = do
  let concrete = evalSymToCon @_ @(RuntimeValue C (ConType a)) model value
  case unRuntimeC concrete of
    Right value' -> Value $ value'
    Left err -> Error err
