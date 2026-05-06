module Effectful.GHC.Annotations
  ( HasAnnotations (..)
  , getAnnotations
  , getFirstAnnotations
  ) where

import GHC.Plugins hiding (getAnnotations, getFirstAnnotations)

import Effectful
import Effectful.Dispatch.Dynamic

import Data.Composition ((.:))
import Data.Word (Word8)
import Data.Maybe (listToMaybe)
import Data.Bifunctor (Bifunctor(..))
import Data.Data (Typeable)

-- | Effect for fetching annotations.
data HasAnnotations :: Effect where
  GetAnnotations
    :: forall a m
     . Typeable a
    => ([Word8] -> a)
    -- ^ Deserialisation function.
    -> ModGuts
    -> HasAnnotations m (ModuleEnv [a], NameEnv [a])

type instance DispatchOf HasAnnotations = Dynamic

-- | Get all annotations of a given type. This happens lazily, that is
-- no deserialization will take place until the [a] is actually demanded and
-- the [a] can also be empty (the UniqFM is not filtered).
--
-- This should be done once at the start of a Core-to-Core pass that uses
-- annotations.
--
-- For more information, check Note [Annotations] in the GHC library.
getAnnotations
  :: forall a es
   . HasAnnotations :> es
  => Typeable a
  => ([Word8] -> a)
  -- ^ Deserialisation function.
  -> ModGuts
  -> Eff es (ModuleEnv [a], NameEnv [a])
getAnnotations = send .: GetAnnotations

-- | Get at most one annotation of a given type per annotatable item.
getFirstAnnotations
  :: forall a es
   . HasAnnotations :> es
  => Typeable a
  => ([Word8] -> a)
  -- ^ Deserialisation function.
  -> ModGuts
  -> Eff es (ModuleEnv a, NameEnv a)
getFirstAnnotations deserialise guts = do
  let mod' = mapMaybeModuleEnv $ const listToMaybe
  let name = mapMaybeNameEnv listToMaybe
  bimap mod' name <$> getAnnotations deserialise guts
