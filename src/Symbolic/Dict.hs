{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Symbolic.Dict
  ( Dict (..)
  , unsafeDict
  , eqNat
  , leqNat
  , posNat
  , cmpNat'
  , someTyNat
  ) where

import GHC.Plugins hiding (empty)
import GHC.TypeLits

import Data.Data (Proxy(..))
import Control.Applicative (Alternative (..))

import Unsafe.Coerce (unsafeCoerce)

data Dict c where
  Dict :: c => Dict c

unsafeDict :: Dict c
unsafeDict = unsafeCoerce $ Dict @()

eqNat
  :: forall l r
   . KnownNat l
  => KnownNat r
  => Maybe (Dict (l ~ r))
eqNat = case cmpNat' @l @r of
  EQI -> pure Dict
  _ -> empty

leqNat
  :: forall l r
   . KnownNat l
  => KnownNat r
  => Maybe (Dict (l <= r))
leqNat = case cmpNat' @l @r of
  LTI -> pure Dict
  EQI -> pure Dict
  _ -> empty

posNat
  :: forall n
   . KnownNat n
  => Maybe (Dict (1 <= n))
posNat = leqNat @1 @n

cmpNat'
  :: forall l r
   . KnownNat l
  => KnownNat r
  => OrderingI l r
cmpNat' = cmpNat @l @r Proxy Proxy

someTyNat :: Type -> Maybe SomeNat
someTyNat ty = do
  num <- isNumLitTy ty
  someNatVal num
