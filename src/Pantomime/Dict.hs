{-# LANGUAGE PolyKinds #-}
-- TODO: We redefine Dict here, but there is the 'constraints' package which has
-- utils for manipulating it. I guess it's better to just import that!

module Pantomime.Dict
  ( Dict (..)
  , unsafeEq
  , eqNat
  , leqNat
  , posNat
  , cmpNat'
  , geqToLeq
  , SomeNat' (..)
  , typeSub
  , typeAdd
  , withSize
  ) where

import GHC.TypeNats

import Data.Constraint (Dict (..))
import Data.Constraint.Unsafe (unsafeAxiom)
import Data.Data (Proxy(..))
import Data.Type.Ord

import Control.Applicative (Alternative (..))
import Control.Monad.Identity (runIdentity)

import Unsafe.Coerce (unsafeCoerce)

unsafeEq :: forall {k} (a :: k) (b :: k). Dict (a ~ b)
unsafeEq = unsafeCoerce $ Dict @(() ~ ())

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

geqToLeq :: forall (n :: Nat) m. n >= m => Dict (m <= n)
-- We only match on the dictionary such that the constraint 'n >= m' does not
-- give a warning about being unused.
geqToLeq = case Dict @(n >= m) of Dict -> unsafeAxiom

-- TODO: This one feels a bit obsolote no? Can't we just split any usage of this
-- into a normal SomeNat and a Dict? Maybe not, but this solution feels very
-- dirty in any case. We should consider looking into a more clean approach.
data SomeNat' eq where
  SomeNat' :: forall n eq. (KnownNat n, n ~ eq) => SomeNat' eq

-- | Type-level subtraction.
typeSub :: forall lhs rhs. KnownNat lhs => KnownNat rhs => SomeNat' (lhs - rhs)
typeSub = runIdentity do
  let lhs' = natVal $ Proxy @lhs
  let rhs' = natVal $ Proxy @rhs
  SomeNat @n _ <- pure . someNatVal $ lhs' - rhs'
  Dict <- pure $ unsafeEq @(lhs - rhs) @n
  pure $ SomeNat' @(lhs - rhs)

-- | Type-level subtraction.
typeAdd :: forall lhs rhs. KnownNat lhs => KnownNat rhs => SomeNat' (lhs + rhs)
typeAdd = runIdentity do
  let lhs' = natVal $ Proxy @lhs
  let rhs' = natVal $ Proxy @rhs
  SomeNat @n _ <- pure . someNatVal $ lhs' + rhs'
  Dict <- pure $ unsafeEq @(lhs + rhs) @n
  pure $ SomeNat' @(lhs + rhs)

-- TODO: Move this thing to Pantomime.Grisette.BitVector
withSize :: forall n r. KnownNat n => (n ~ 0 => r) -> (1 <= n => r) -> r
withSize con sym = case natVal $ Proxy @n of
  0 -> case unsafeEq @n @0 of Dict -> con
  _ -> case unsafeAxiom @(1 <= n) of Dict -> sym
