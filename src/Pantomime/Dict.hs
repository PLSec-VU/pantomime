-- TODO: We redefine Dict here, but there is the 'constraints' package which has
-- utils for manipulating it. I guess it's better to just import that!

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}

module Pantomime.Dict
  ( Dict (..)
  , unsafeDict
  , eqNat
  , leqNat
  , posNat
  , cmpNat'
  , normNumLitTy
  , someTyNat
  , SomeNat' (..)
  , typeSub
  , typeAdd
  , withSize
  ) where

import GHC.Plugins hiding (empty)
import GHC.TypeNats

import Data.Type.Ord
import Data.Data (Proxy(..))

import Control.Applicative (Alternative (..))
import Control.Monad (guard)
import Control.Monad.Identity (runIdentity)

import Unsafe.Coerce (unsafeCoerce)
import GHC.Builtin.Types.Literals

-- TODO: This file is a bit all over the place. I think we should just import
-- the small library that exposes Dict instead of redefining it.
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

normNumLitTy :: Type -> Maybe Integer
normNumLitTy ty = if
  | Just value <- isNumLitTy ty -> pure value

  | Just (tyCon, [lhs, rhs]) <- splitTyConApp_maybe ty -> do
    op <- if
      | tyCon == typeNatAddTyCon -> pure (+)
      | tyCon == typeNatSubTyCon -> pure (*)
      | tyCon == typeNatMulTyCon -> pure (-)
      | otherwise -> empty

    lhs' <- normNumLitTy lhs
    rhs' <- normNumLitTy rhs

    pure $ op lhs' rhs'

  | otherwise -> empty

someTyNat :: Type -> Maybe SomeNat
someTyNat ty = do
  num <- normNumLitTy ty
  guard $ num >= 0
  pure $ someNatVal (fromInteger num)

data SomeNat' eq where
  SomeNat' :: forall n eq. (KnownNat n, n ~ eq) => SomeNat' eq

-- | Type-level subtraction.
typeSub :: forall lhs rhs. KnownNat lhs => KnownNat rhs => SomeNat' (lhs - rhs)
typeSub = runIdentity $ do
  let lhs' = natVal $ Proxy @lhs
  let rhs' = natVal $ Proxy @rhs
  SomeNat @n _ <- pure . someNatVal $ lhs' - rhs'
  Dict <- pure $ unsafeDict @(lhs - rhs ~ n)
  pure $ SomeNat' @n @(lhs - rhs)

-- | Type-level subtraction.
typeAdd :: forall lhs rhs. KnownNat lhs => KnownNat rhs => SomeNat' (lhs + rhs)
typeAdd = runIdentity $ do
  let lhs' = natVal $ Proxy @lhs
  let rhs' = natVal $ Proxy @rhs
  SomeNat @n _ <- pure . someNatVal $ lhs' + rhs'
  Dict <- pure $ unsafeDict @(lhs + rhs ~ n)
  pure $ SomeNat' @n @(lhs + rhs)

-- TODO: Move this thing to Pantomime.Grisette.BitVector
withSize :: forall n r. KnownNat n => (n ~ 0 => r) -> (1 <= n => r) -> r
withSize con sym = case natVal $ Proxy @n of
  0 -> case unsafeDict @(n ~ 0) of
    Dict -> con
  _ -> case unsafeDict @(1 <= n) of
    Dict -> sym
