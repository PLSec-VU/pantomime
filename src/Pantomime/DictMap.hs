-- | A map from 'Typeable' types to a 'Constraint' that this type satisfies.
--
-- To ensure valid mappings from types to dictionaries, both keys and values
-- are not passed in as value-level arguments. Instead, a key is passes by
-- type application. The value is always the canonical 'Constraint' that
-- corresponds to this type. That is, if constraints are coherent (i.e. no
-- 'IncoherentConstraints'), then there exists only a single value for each key.
--
-- This module is intended to be imported qualified, to avoid name clashes with
-- Prelude functions, e.g.
--
-- > import Data.Map (Map)
-- > import qualified Data.Map as Map
module Pantomime.DictMap
  ( DictMap
  , empty
  , lookup
  , insert
  , delete
  , delete'
  ) where

import Prelude (($), maybe, pure)

import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap

import Data.Kind (Type)
import Data.Typeable
import Data.Constraint

import Control.Error (LookupError (..))

import Unsafe.Coerce (unsafeCoerce)

import Effectful
import Effectful.Error.Static

-- | Dictionary map.
--
-- This permits lookups of typeclass instances in the map.
newtype DictMap (c :: Type -> Constraint) where
  DictMap :: HashMap TypeRep (Entry c) -> DictMap c

-- | Entry for the dictionary map.
--
-- This existential quantifier hides the type of the inner constraint to allow
-- for a heterogenous container. Altough we cannot enforce it through the type
-- system, the type of an entry should always correspond to the type of the key
-- that indexes it.
data Entry (c :: Type -> Constraint) where
  Entry :: forall a c. c a => Entry c

-- | Construct an empty dictionary map.
empty :: DictMap c
empty = DictMap HashMap.empty

-- | Return the dictionary that is mapped by the given key.
--
-- Note that the key is given by the 'Typeable' instance and is thus not passed
-- explicitly.
lookup
  :: forall k c es
   . Error (LookupError TypeRep) :> es
  => Typeable k
  => DictMap c
  -> Eff es (Dict (c k))
lookup (DictMap map) = do
  -- Lookup the entry.
  let key = typeRep @_ @k Proxy
  let result = HashMap.lookup key map
  let err = throwError $ LookupError key
  Entry @e <- maybe err pure result

  -- SAFETY: An invariant of the dictionary map is that all key-value pairs are
  -- of the same type. We cannot ensure this through the type system however,
  -- so we have to coerce unsafely.
  Refl <- pure $ unsafeEqT @k @e
  pure Dict

-- | Unsafely extract a witness of equality of two types.
unsafeEqT :: forall a b. a :~: b
unsafeEqT = unsafeCoerce Refl

-- TODO: I should make an item like Entry available (with a typeable
-- constraint), such that we can create an insertMany function.

-- | Insert a typeclass constraint into the map for the type of the key.
--
-- The key and value are derived from the typeclass constraints on the key. The
-- key is thus not passes as value-level argument. Instead, it is expected that
-- the key is selected by type application.
--
-- > let map' = insert @Int map
insert
  :: forall k c
   . Typeable k
  => c k
  => DictMap c
  -> DictMap c
insert (DictMap map) = do
  let key = typeRep @_ @k Proxy
  let value = Entry @k
  DictMap $ HashMap.insert key value map

-- | Delete a typeclass constraint from the dictionary map.
--
-- The key is derived from the 'Typeable' constraint. Instead of passing it as
-- a normal argument, one is expected to use type applications to select the
-- appropriate type.
--
-- > let map' = delete @Int map
delete
  :: forall k c
   . Typeable k
  => DictMap c
  -> DictMap c
delete map = do
  let key = typeRep @_ @k Proxy
  delete' key map

-- | Delete a typeclass constraint from the dictionary map.
--
-- > let map' = delete' (typeRep @_ @Int Proxy) map
delete'
  :: forall c
   . TypeRep
  -> DictMap c
  -> DictMap c
delete' key (DictMap map) = do
  DictMap $ HashMap.delete key map
