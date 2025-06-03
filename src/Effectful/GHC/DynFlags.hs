{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Effectful.GHC.DynFlags
  ( HasDynFlagsE (..)
  ) where

import Effectful
import Effectful.Dispatch.Dynamic (send)

import GHC.Plugins (DynFlags, HasDynFlags (..))

-- | Effect to get 'DynFlags'.
data HasDynFlagsE :: Effect where
  GetDynFlags :: HasDynFlagsE m DynFlags

type instance DispatchOf HasDynFlagsE = Dynamic

-- | WARNING: Although canonical, this is an orphan instance. This might clash
-- with other effects that define instances for it.
instance HasDynFlagsE :> es => HasDynFlags (Eff es) where
  getDynFlags = send GetDynFlags

