{-# LANGUAGE DataKinds #-}

module Symbolic.Clash.Util
  ( lookupThId
  , lookupThTyCon
  , concreteNat
  ) where

import GHC.Plugins hiding (empty)
import GHC.Types.TyThing (MonadThings (..))
import GHC.TypeNats
import GHC.Data.Maybe (rightToMaybe)
import GHC.Core.TyCo.Compare (eqType)
import GHC.MonadCore

import qualified Language.Haskell.TH as TH

import Grisette (ToCon(..), WordN)
import Grisette.Unified (EvalModeTag (..))

import Control.Monad (guard)
import Control.Applicative (Alternative (empty))

import Util

import Symbolic.Value
import Symbolic.WordSize
import Symbolic.Runtime

lookupThId
  :: MonadCore m
  => MonadFail m
  => TH.Name
  -> m Var
lookupThId th = do
  name <- thNameToGhcName' th
    ??= "Lookup failed."
  liftCore $ lookupId name

lookupThTyCon
  :: MonadCore m
  => MonadFail m
  => TH.Name
  -> m TyCon
lookupThTyCon th = do
  name <- thNameToGhcName' th
    ??= "Lookup failed."
  liftCore $ lookupTyCon name

concreteNat
  :: forall m ws
   . KnownWordSize ws
  => ADT m ws
  -> Maybe Natural
concreteNat adt = do
  guard $ adtType adt `eqType` naturalTy

  rtag <- toCon @_ @(Tag C ws) $ adtTag adt
  tag <- rightToMaybe $ unRuntimeC rtag
  dataCon <- tagToDataCon tag $ adtTyCon adt

  fields <- adtDataConFields adt dataCon
  case fields of
    [Primitive (Word value)] | dataCon == naturalNSDataCon -> do
      rvalue <- toCon @_ @(RuntimeValue C (WordN (WordBits ws))) value
      value' <- rightToMaybe $ unRuntimeC rvalue
      pure $ fromIntegral value'
    [Primitive (ByteArray _ value)] | dataCon == naturalNBDataCon -> do
      rvalue <- toCon @_ @(RuntimeValue C Integer) value
      value' <- rightToMaybe $ unRuntimeC rvalue
      pure $ fromIntegral value'
    _ -> empty
