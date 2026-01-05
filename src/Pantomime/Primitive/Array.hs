module Pantomime.Primitive.Array
  ( Array
  , select
  , store
  , const
  ) where

import Data.Coerce (coerce)
import Prelude (($), undefined)
import Grisette.Internal.SymPrim.Array qualified as Inner

newtype Array k v where
  Array :: Inner.Array k v -> Array k v

-- TODO: I guess I need some way to specify only primitives can actually be
-- stored. Probably the best way to do this is to create a typeclass 'Primitive'
-- that I hide such that only my types can implement it. Then I just do some
-- internal magic to reconstruct the typeclass constraints I actually need.
{-# OPAQUE select #-}
select :: forall k v. Array k v -> k -> v
select = undefined

{-# OPAQUE store #-}
store :: forall k v. Array k v -> k -> v -> Array k v
store = undefined

{-# OPAQUE const #-}
const :: forall k v. v -> Array k v
const = coerce $ Inner.const @k @v
