{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Symbolic.Clash.Util
  ( lookupThId
  , lookupThTyCon
  , concreteNat
  , symShiftL'
  , symShiftRL'
  , symShiftRA'
  ) where

import GHC.Plugins hiding (empty)
import GHC.Types.TyThing (MonadThings (..))
import GHC.TypeNats
import GHC.Data.Maybe (rightToMaybe)
import GHC.Core.TyCo.Compare (eqType)
import GHC.MonadCore

import qualified Language.Haskell.TH as TH

import Grisette (ToCon(..), WordN, SymIntN, SymShift (..), SymFromIntegral (..))
import Grisette.Unified (EvalModeTag (..))

import Control.Monad (guard)
import Control.Applicative (Alternative (empty))

import Util

import Symbolic.Value
import Symbolic.WordSize
import Symbolic.Runtime
import Symbolic.Sized.BitVector

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

symShiftL'
  :: forall bv ws (n :: Natural)
   . SymFromIntegral (SymIntN (WordBits ws)) (bv n)
  => SymShift (bv n)
  => bv n
  -> SymInt ws
  -> bv n
symShiftL' value (SymInt idx) = do
  let idx' = symFromIntegral idx
  symShift value idx'

symShiftRL'
  :: forall bv ws n
   . KnownNat n
  => KnownWordSize ws
  => SymFromIntegral (WordN' S n) (bv n)
  => SymFromIntegral (bv n) (WordN' S n)
  => bv n
  -> SymInt ws
  -> bv n
symShiftRL' value (SymInt idx) = do
  let idx' = symFromIntegral idx

  let value' = symFromIntegral value :: WordN' S n
  -- TODO: Same thing as with 'symShiftL' (i.e. non-total function)
  let result = symShiftNegated value' idx'
  symFromIntegral result

symShiftRA'
  :: forall bv ws n
   . KnownNat n
  => KnownWordSize ws
  => SymFromIntegral (IntN' S n) (bv n)
  => SymFromIntegral (bv n) (IntN' S n)
  => bv n
  -> SymInt ws
  -> bv n
symShiftRA' value (SymInt idx) = do
  let idx' = symFromIntegral idx

  let value' = symFromIntegral value :: IntN' S n
  -- TODO: Same thing as with 'symShiftL' (i.e. non-total function)
  let result = symShiftNegated value' idx'
  symFromIntegral result
