{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Effectful.GHC.Display
  ( Display (..)
  , display
  , debug
  , debugS
  ) where

import Data.Composition ((.:))
import Effectful
import Effectful.Dispatch.Dynamic (send)

import GHC.Utils.Outputable (Outputable (..), SDoc, text)
import GHC.Types.Error (MessageClass (..))


-- | Effect to get display 'SDoc'.
data Display :: Effect where
  Display :: MessageClass -> SDoc -> Display m ()

type instance DispatchOf Display = Dynamic

-- | Output a message using the 'Display' effect.
display
  :: forall es
   . Display :> es
  => MessageClass
  -> SDoc
  -> Eff es ()
display = send .: Display

-- TODO: Add the remaining output functions that are also available via GHC.

-- | Output a debugging message using the 'Display' effect.
debug
  :: forall o es
   . Display :> es
  => Outputable o
  => o
  -> Eff es ()
debug = display MCDump . ppr

-- | Output a 'String' debugging message using the 'Display' effect.
debugS
  :: forall es
   . Display :> es
  => String
  -> Eff es ()
debugS = debug . text @SDoc
