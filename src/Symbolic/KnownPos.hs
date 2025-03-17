{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Symbolic.KnownPos
  ( KnownPos
  ) where

import GHC.TypeLits (KnownNat, type (<=))

type KnownPos n = (KnownNat n, 1 <= n)
