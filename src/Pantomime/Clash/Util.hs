{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Pantomime.Clash.Util
  ( lookupThId
  , lookupThTyCon
  , concreteNat
  , mkNatTyVarTy
  ) where

import GHC.Plugins hiding (empty, thNameToGhcName)
import GHC.Types.TyThing (MonadThings (..))
import GHC.TypeNats
import GHC.Data.Maybe (rightToMaybe)
import GHC.Core.TyCo.Compare (eqType)

import Language.Haskell.TH qualified as TH

import Grisette (ToCon(..))
import Grisette.Unified (EvalModeTag (..))

import Control.Monad (guard)
import Control.Applicative (Alternative (empty))
import Control.Error

import Pantomime.Value
import Pantomime.WordSize
import Pantomime.Runtime

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
      rvalue <- toCon @_ @(RuntimeValue C (WordPW C ws)) value
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
