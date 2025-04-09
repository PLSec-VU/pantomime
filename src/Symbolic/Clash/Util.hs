module Symbolic.Clash.Util
  ( lookupThId
  , lookupThTyCon
  ) where

import GHC.Plugins
import GHC.Types.TyThing (MonadThings (..))
import GHC.MonadCore

import qualified Language.Haskell.TH as TH

import Util

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

