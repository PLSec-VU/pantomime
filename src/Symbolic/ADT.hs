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
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}

module Symbolic.ADT
  ( ADT (..)
  , mkADT
  , adtType
  , untypedField
  , adtIsDataCon
  , eqTyADT

  , Tag (..)
  , tagToDataCon
  , dataConToTag
  , accessTag
  , tagInRange

  , dataConAccessorNames
  ) where

import GHC.Plugins
import GHC.Core.TyCo.Compare (eqType)

import Grisette.Unified (EvalModeTag (..), EvalModeAll, GetBool, BaseMonad)
import Grisette.Internal.Unified.UnifiedBV (UnifiedBVImpl(..))
import Grisette
  ( EvalSym (..)
  , EvalSym1
  , ToCon (..)
  , ToSym (..)
  , Mergeable
  , LogicalOp (..)
  , SymEq (..)
  , SymOrd (..)
  , mrgPure
  )

import Data.Foldable (find)
import Data.Maybe (fromJust)

import Control.Monad.Except (MonadError(..))
import Control.Monad (guard, unless)

import Symbolic.Runtime
import Symbolic.WordSize
import Symbolic.Identifier
import Symbolic.Util
import Symbolic.MonadEval

-- | Abstract Data Type.
--
-- This may both be symbolic or concrete depending on its mode parameter. Note
-- that this is more or less an SMT-like encoding.
data ADT mode where
  ADT
    :: TyCon
    -> [Type]
    -> RuntimeValue mode (Ident mode)
    -> ADT mode

instance Outputable (ADT C) where
  ppr adt@(ADT _ _ value) = ppr (adtType adt) <+> "=>" <+> text (show value)

instance Outputable (ADT S) where
  ppr adt@(ADT _ _ value) = ppr (adtType adt) <+> "=>" <+> text (show value)

instance (EvalSym1 (BaseMonad mode), EvalSym (Ident mode)) => EvalSym (ADT mode) where
  evalSym fillDefault model (ADT tyCon tys ident) = do
    let ident' = evalSym fillDefault model ident
    ADT tyCon tys ident'

instance ToCon (ADT S) (ADT C) where
  toCon (ADT tyCon tys value) = ADT tyCon tys <$> toCon value 

instance ToSym (ADT C) (ADT S) where
  toSym (ADT tyCon tys value) = ADT tyCon tys $ toSym value

instance MonadEval m => StrictIte m (ADT S) where
  strictIte cond tr@(ADT tc tys tval) fl@(ADT _ _ fval) = do
    unless (eqTyADT tr fl) $ throwError IllTyped
    ADT tc tys <$> strictIte cond tval fval

instance MonadEval m => StrongEq m (ADT S) where
  strongEq lhs@(ADT _ _ lval) rhs@(ADT _ _ rval) = do
    unless (eqTyADT lhs rhs) $ throwError IllTyped
    strongEq lval rval

instance Assume (ADT S) where
  assume cond (ADT tyCon tys ident) = ADT tyCon tys $ assume cond ident

-- | Create an ADT.
--
-- Prefer using this function over manual construction, as it additionally adds
-- the assumption that its tag should be in range.
mkADT
  :: forall ws
   . KnownWordSize ws
  => TyCon
  -> [Type]
  -> RuntimeValue S (Ident S)
  -> ADT S
mkADT tyCon tys ident = do
  let adt = ADT tyCon tys ident
  let tag = accessTag @ws adt
  -- TODO: I'm unsure about this conditional. I think it is too strict, as it
  -- does not allow for the ADT iself to be invalid.
  let conditional = tagInRange tag .== pure true
  assume conditional adt

-- | Get the type of this ADT.
adtType :: ADT mode -> Type
adtType (ADT tyCon tys _) = mkTyConApp tyCon tys

-- | Accessor for a field of an ADT.
--
-- Note that the result can be resolved to any type, so care should be taken
-- to ensure the accessor is correctly typed.
untypedField
  :: forall t
   . Mergeable t
  => Interpretable t
  => ADT S
  -> String
  -- TODO: I think this input String should really be Text...
  -> RuntimeValue S t
untypedField (ADT _ _ value) name = interpretWith value name

-- | Whether the given ADT matches the DataCon.
--
-- Note, this does not typecheck whether the ADT actually matches the DataCon.
adtIsDataCon
  :: forall ws
   . KnownWordSize ws
  => ADT S
  -> DataCon
  -> Maybe (RuntimeValue S (GetBool S))
adtIsDataCon adt dataCon = do
  -- Gather the field from the ADT and create a tag instance from the DataCon.
  let Tag lty lhs = accessTag @ws adt
  let Tag rty rhs = dataConToTag dataCon

  -- Ensure the type constructors match.
  guard $ lty == rty

  -- The actual equality check.
  pure $ do
    lhs' <- lhs
    rhs' <- rhs
    mrgPure $ lhs' .== rhs'

-- | Check whether the ADT have matching types.
eqTyADT
  :: ADT mode
  -> ADT mode
  -> Bool
eqTyADT lhs rhs = adtType lhs `eqType` adtType rhs

-- | Tag of an ADT, used to distinguish between constructors.
--
-- Note that this is more or less an SMT encoded DataCon. This can either be
-- concrete or symbolic, based on its evaluation mode.
data Tag mode ws where
  Tag
    :: TyCon
    -> RuntimeValue mode (GetIntN mode (WordBits ws))
    -- ^ We use the platform sized integer as tag, since Haskell specifically
    -- has a primitive function to convert these into a typed DataCon.
    --
    -- TODO: I think we should use our platform width newtype here, once we add
    -- support for its eval mode.
    -> Tag mode ws

instance KnownWordSize ws => Outputable (Tag C ws) where
  ppr (Tag tyCon value) = ppr tyCon <+> "=>" <+> text (show value)

instance KnownWordSize ws => Outputable (Tag S ws) where
  ppr (Tag tyCon value) = ppr tyCon <+> "=>" <+> text (show value)

instance (EvalSym1 (BaseMonad mode), EvalSym (GetIntN mode (WordBits ws))) => EvalSym (Tag mode ws) where
  evalSym fillDefault model (Tag tyCon value) = do
    let value' = evalSym fillDefault model value
    Tag tyCon value'

instance KnownWordSize ws => ToCon (Tag S ws) (Tag C ws) where
  toCon (Tag tyCon value) = Tag tyCon <$> toCon value

instance KnownWordSize ws => ToSym (Tag C ws) (Tag S ws) where
  toSym (Tag tyCon value) = Tag tyCon $ toSym value

instance (MonadEval m, KnownWordSize ws) => StrictIte m (Tag S ws) where
  strictIte cond (Tag ttc tval) (Tag ftc fval) = do
    unless (ttc == ftc) $ throwError IllTyped
    Tag ttc <$> strictIte cond tval fval

instance (MonadEval m, KnownWordSize ws) => StrongEq m (Tag S ws) where
  strongEq (Tag ltc lval) (Tag rtc rval) = do
    unless (ltc == rtc) $ throwError IllTyped
    strongEq lval rval

instance (MonadEval m, KnownWordSize ws) => WeakEq m (Tag S ws) where
  weakEq (Tag ltc lval) (Tag rtc rval) = do
    unless (ltc == rtc) $ throwError IllTyped
    weakEq lval rval

instance KnownWordSize ws => Assume (Tag S ws) where
  assume cond (Tag tyCon value) = Tag tyCon $ assume cond value

-- | Get the DataCon from a Tag and the Type that should match the .
tagToDataCon
  :: forall ws
   . KnownWordSize ws
  => Tag C ws
  -> RuntimeValue C DataCon
tagToDataCon (Tag tyCon tag) = do
  -- Tags should only have type constructors with DataCons. If this fails, it is
  -- a bug and we might as well fail fast.
  let dataCons = fromJust $ tyConDataCons_maybe tyCon
  tag' <- tag
  let cmp = (tag' ==) . fromIntegral . dataConTagZ

  -- An invalid tag should be unreachable. Note that this actually makes sense
  -- as a valid return for vacuous types.
  whyFail Invalid $ find cmp dataCons

-- | Get the symbolic representation of the DataCon.
dataConToTag
  :: forall mode ws
   . EvalModeAll mode
  => KnownWordSize ws
  => DataCon
  -> Tag mode ws
dataConToTag dataCon = do
  let tyCon = dataConTyCon dataCon
  let val = fromIntegral $ dataConTagZ dataCon
  Tag tyCon $ pure val

-- | Accessor for the tag of an ADT.
accessTag
  :: forall ws
   . KnownWordSize ws
  => ADT S
  -> Tag S ws
accessTag adt = do
  let (ADT tyCon _ _) = adt
  Tag tyCon $ untypedField adt "!tag"

-- | Boolean denoting when an ADT has a tag that is in-range.
--
-- This may, for example, be used to assume that an ADT represents any valid
-- DataCon.
tagInRange
  :: forall ws
   . KnownWordSize ws
  => Tag S ws
  -> RuntimeValue S (GetBool S)
tagInRange (Tag tyCon value) = do
  let amount = length $ tyConDataCons tyCon
  value' <- value
  -- TODO: Once Grisette adds support for (.&&), we could parameterise on the
  -- evaluation mode. We could of course implement this (.&&) ourselves already,
  -- but we leave it for now.
  mrgPure $ 0 .<= value' .&& value' .< fromIntegral amount

-- | Get the accessor names of this DataCon.
--
-- For a DataCon with unnamed fields, this will return enumerated names instead
-- as a default.
dataConAccessorNames :: DataCon -> [String]
dataConAccessorNames dataCon = do
  -- TODO: Note sure if we want to emit fields with pprUnsafe. I think we just
  -- want the plain old name as typed in Haskell.
  -- TODO: It is actually complete nonsense to want to emit these named fields
  -- like this for records. Only the solver sees these, so just numbered fields
  -- will do this just fine.
  let names = showPprUnsafe . flSelector <$> dataConFieldLabels dataCon
  let arity = dataConRepArity dataCon
  if
    | arity > length names -> show <$> [0..arity-1]
    | otherwise -> names
