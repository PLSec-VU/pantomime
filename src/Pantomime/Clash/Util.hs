{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Pantomime.Clash.Util
  ( lookupThId
  , lookupThTyCon
  , concreteNat
  , mkNatTyVarTy
  , symShiftL'
  , symShiftRL'
  , symShiftRA'
  ) where

import GHC.Plugins hiding (empty, thNameToGhcName)
import GHC.Types.TyThing (MonadThings (..))
import GHC.TypeNats
import GHC.Data.Maybe (rightToMaybe)
import GHC.Core.TyCo.Compare (eqType)

import Language.Haskell.TH qualified as TH

import Grisette (ToCon(..), WordN, SymIntN, SymShift (..), SymFromIntegral (..))
import Grisette.Unified (EvalModeTag (..))

import Control.Monad (guard)
import Control.Applicative (Alternative (empty))
import Control.Error

import Pantomime.Value
import Pantomime.WordSize
import Pantomime.Runtime
import Pantomime.Grisette.BitVector qualified as Pantomime

import Effectful
import Effectful.GHC.TH
import Effectful.Error.Static (Error)
import Effectful.GHC.TyThing

lookupThId
  :: Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => TH.Name
  -> Eff es Var
lookupThId th = do
  name <- thNameToGhcName th
  lookupId name

lookupThTyCon
  :: Error (LookupError Name) :> es
  => Error (LookupError TH.Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => TH.Name
  -> Eff es TyCon
lookupThTyCon th = do
  name <- thNameToGhcName th
  lookupTyCon name

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

-- | Create a type-variable type with the natural kind.
mkNatTyVarTy :: TyVar -> Type
mkNatTyVarTy tyVar = mkTyVarTy $ setVarType tyVar naturalTy

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
  => SymFromIntegral (Pantomime.WordN S n) (bv n)
  => SymFromIntegral (bv n) (Pantomime.WordN S n)
  => bv n
  -> SymInt ws
  -> bv n
symShiftRL' value (SymInt idx) = do
  let idx' = symFromIntegral idx

  let value' = symFromIntegral value :: Pantomime.WordN S n
  -- TODO: Same thing as with 'symShiftL' (i.e. non-total function)
  let result = symShiftNegated value' idx'
  symFromIntegral result

symShiftRA'
  :: forall bv ws n
   . KnownNat n
  => KnownWordSize ws
  => SymFromIntegral (Pantomime.IntN S n) (bv n)
  => SymFromIntegral (bv n) (Pantomime.IntN S n)
  => bv n
  -> SymInt ws
  -> bv n
symShiftRA' value (SymInt idx) = do
  let idx' = symFromIntegral idx

  let value' = symFromIntegral value :: Pantomime.IntN S n
  -- TODO: Same thing as with 'symShiftL' (i.e. non-total function)
  let result = symShiftNegated value' idx'
  symFromIntegral result
