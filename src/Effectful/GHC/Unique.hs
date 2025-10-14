{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Effectful.GHC.Unique
  ( HasUnique (..)
  , MonadUnique (..)
  ) where

import Effectful (type (:>), Eff, Effect, DispatchOf, Dispatch (..))
import Effectful.Dispatch.Dynamic (send)

import GHC.Types.Unique.Supply (MonadUnique (..), UniqSupply)

-- | Effect to get 'Unique' values.
data HasUnique :: Effect where
  GetUniqueSupply :: HasUnique m UniqSupply

type instance DispatchOf HasUnique = Dynamic

-- | WARNING: Although canonical, this is an orphan instance. This might clash
-- with other effects that define instances for it.
instance HasUnique :> es => MonadUnique (Eff es) where
  getUniqueSupplyM = send GetUniqueSupply
