{-# LANGUAGE BangPatterns #-}

module Data.Sum
  ( Sum
  , type (>-)
  , weaken
  , raise
  , embed
  , absurd
  ) where

import Data.Kind (Type)
import Data.Member (type (>-) (..))
import GHC.Types (Any)
import Unsafe.Coerce (unsafeCoerce)

-- | An value that inhabits one of the types in @ts@.
data Sum (ts :: [Type]) where
  Sum :: !Int -> Any -> Sum ts

-- | Weaken a 'Sum' by handling one of its cases.
weaken
  :: forall t ts
   . Sum (t : ts)
  -> Either t (Sum ts)
weaken (Sum idx err) = case idx of
  0 -> Left $ unsafeCoerce @_ @t err
  _ -> Right $ Sum (idx - 1) err

-- | Raise a 'Sum' to encompass more values.
raise
  :: forall t ts
   . Sum ts
  -> Sum (t : ts)
raise (Sum idx err) = Sum (idx + 1) err

-- | Embed a value into a 'Sum'.
embed
  :: forall t ts
   . t >- ts
  => t
  -> Sum ts
embed = Sum (reifyIndex @_ @t @ts) . unsafeCoerce

-- | There are no inhabitants for this error type.
absurd :: Sum '[] -> a
absurd !_ = error "variant with empty type list is uninhabited"
