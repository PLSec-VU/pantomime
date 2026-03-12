{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Member
  ( type (>-) (..)
  ) where

import GHC.TypeLits (TypeError, ErrorMessage (..))

-- | A constraint that requires a particular type @t@ to be a member of the
-- type-level list @ts@.
class (t :: k) >- (ts :: [k]) where
  reifyIndex :: Int

instance TypeError
  ( Text "Type '" :<>: ShowType t :<>: Text "' does not occur in the context"
  ) => t >- '[] where
  reifyIndex = error "unreachable"

instance {-# OVERLAPPING #-} t >- (t : es) where
  reifyIndex = 0

instance t >- ts => t >- (u : ts) where
  reifyIndex = 1 + reifyIndex @_ @t @ts
