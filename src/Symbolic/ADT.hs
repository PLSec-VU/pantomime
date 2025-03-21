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
  ( SymADT
  , ADT

  , SymTag
  , Tag

  , tagToDataCon
  , dataConToTag

  , adtIsDataCon
  , tagInRange

  , Solvable' (..)
  , accessTag
  , accessField

  , dataConAccessorNames
  ) where

import GHC.Plugins

import Grisette
import Grisette.Internal.SymPrim.Prim.Term (SupportedNonFuncPrim)

import Data.Data (Typeable)
import Data.Foldable (find)
import Data.Hashable (Hashable)
import Data.String (IsString(..))

import Symbolic.Runtime
import Symbolic.WordSize

-- TODO: I think it would be good to make the ADT type always carry its type.
-- Not just inside of a Value.

-- | Symbolic Abstract Data type.
type SymADT = SymWordN64

-- | Concrete representation of Abstract Data type.
--
-- Note, that this is the SMT encoded representation.
type ADT = WordN64

-- | Symbolic ADT Tag to distinguish between constructors.
type SymTag ws = SymIntN (WordBits ws)

-- | Conrete representation of ADT Tag.
--
-- Note, that this is the SMT encoded representation.
type Tag ws = IntN (WordBits ws)

-- | Get the DataCon from a Tag and the Type that should match the .
tagToDataCon
  :: forall ws
   . KnownWordSize ws
  => Tag ws
  -> Type
  -> Maybe DataCon
tagToDataCon tag ty = do
  (tyCon, _) <- splitTyConApp_maybe ty
  dataCons <- tyConDataCons_maybe tyCon
  let cmp dataCon = dataConToTag dataCon == tag
  find cmp dataCons

-- | Get the symbolic representation of the DataCon.
dataConToTag :: KnownWordSize ws => DataCon -> Tag ws
dataConToTag = fromIntegral . dataConTagZ

-- | Whether the given ADT matches the DataCon.
--
-- Note, this does not typecheck whether the ADT actually matches the DataCon.
-- TODO: I do want this to perform a typecheck! I would need to include the
-- type on an ADT first.
adtIsDataCon
  :: forall ws
   . KnownWordSize ws
  => RuntimeValue SymADT
  -> DataCon
  -> RuntimeValue SymBool
adtIsDataCon adt dataCon = do
  field <- accessTag @ws adt
  let tag = con $ dataConToTag dataCon
  mrgReturn $ field .== tag

-- | Accessor for the tag of an ADT.
accessTag
  :: forall ws
   . KnownWordSize ws
  => RuntimeValue SymADT
  -> RuntimeValue (SymTag ws)
accessTag adt = accessField adt "!tag"

-- class Solvable (c t => Solvable' c t | t -> c where
--   sym' :: Symbol -> t

-- instance (Solvable c t, LinkedRep c t, SupportedNonFuncPrim c, Show c, Hashable c, Typeable c) => Solvable' (ADT --> c) (SymADT -~> t) where
--   sym' = sym

-- | Solvable class to avoid overlapping instances on 'accessField'.
-- TODO: Is this really the best way to resolve the overlapping instance? It
-- works for now...
class
  ( Solvable c t
  , LinkedRep c t
  , SupportedNonFuncPrim c
  , Show c
  , Hashable c
  , Typeable c
  , Solvable (ADT --> c) (SymADT -~> t)
  ) => Solvable' c t | t -> c where
  sym' :: Symbol -> (SymADT -~> t)

instance
  ( Solvable c t
  , LinkedRep c t
  , SupportedNonFuncPrim c
  , Show c
  , Hashable c
  , Typeable c
  ) => Solvable' c t where
  sym' = sym

-- | Accessor for a field of an ADT.
--
-- Note that the result can be resolved to any type, so care should be taken
-- to ensure the accessor is correctly typed.
accessField
  :: forall c t
   . Solvable' c t
  => RuntimeValue SymADT
  -> String
  -- TODO: I think this input String should really be Text...
  -> RuntimeValue t
accessField adt name = do
  let symbol = simple . identifier . fromString $ name
  let accessor = sym' symbol :: SymADT -~> t
  adt' <- adt
  pure $ accessor # adt'

-- | Boolean denoting when an ADT has a tag that is in-range.
--
-- This may, for example, be used to assume that an ADT represents any valid
-- DataCon.
tagInRange
  :: forall ws
   . KnownWordSize ws
  => Type
  -> RuntimeValue SymADT
  -> RuntimeValue SymBool
tagInRange ty adt = do
  let (tyCon, _) = splitTyConApp ty
  let amount = length $ tyConDataCons tyCon
  tag <- accessTag @ws adt
  mrgPure $ 0 .<= tag .&& tag .< fromIntegral amount

-- | Get the accessor names of this DataCon.
--
-- For a DataCon with unnamed fields, this will return enumerated names instead
-- as a default.
dataConAccessorNames :: DataCon -> [String]
dataConAccessorNames dataCon = do
  -- TODO: Note sure if we want to emit fields with pprUnsafe. I think we just
  -- want the plain old name as typed in Haskell.
  let names = showPprUnsafe . flSelector <$> dataConFieldLabels dataCon
  let arity = dataConRepArity dataCon
  if
    | arity > length names -> show <$> [0..arity-1]
    | otherwise -> names

