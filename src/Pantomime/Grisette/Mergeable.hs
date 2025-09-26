module Pantomime.Grisette.Mergeable
  ( partialStrategy
  , ifStrategy
  , tupleStrategy
  , impossible
  ) where

import GHC.Stack (HasCallStack)

import Data.Either (isLeft)

import Grisette
  ( MergingStrategy (..)
  , product2Strategy
  , wrapStrategy
  )

-- | Partial merging strategy.
--
-- Sometimes we do not want to (or cannot) merge values. This function allows
-- one to encode which states are mergeable. The remaining patterns will receive
-- 'NoStrategy' as merging strategy.
partialStrategy
  :: (r -> a)
  -> (a -> Maybe r)
  -> MergingStrategy r
  -> MergingStrategy a
partialStrategy wrap unwrap strategy = do
  wrapStrategy
    -- Use inner merging strategy only if possible.
    (ifStrategy
      isLeft
      NoStrategy
      (wrapStrategy
        strategy
        Right
        \case Right value -> value; _ -> impossible))

    -- Wrap unmergeable value in Left and mergeable ones in Right.
    (either id wrap)

    -- Unwrap from original value or merged one.
    (\value -> maybe (Left value) Right $ unwrap value)

-- | If strategy.
--
-- Depending on a predicate on a mergeable value, use either the first or the
-- second strategy.
ifStrategy
  :: (a -> Bool)
  -> MergingStrategy a
  -> MergingStrategy a
  -> MergingStrategy a
ifStrategy f true false = SortedStrategy f \case
  True -> true
  False -> false

-- | Product strategy specialised to a tuple.
tupleStrategy
  :: MergingStrategy a
  -> MergingStrategy b
  -> MergingStrategy (a, b)
tupleStrategy = product2Strategy (,) id

-- | Marker to use for unreachable branches in merging strategies.
impossible :: HasCallStack => a
impossible = error "BUG: sorted strategy should ensure this path is unreachable"
