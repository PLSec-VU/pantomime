module Pantomime.Grisette.Mergeable
  ( NoMerge (..)
  , NoEval (..)
  , partialStrategy
  , ifStrategy
  , tupleStrategy
  , impossible
  ) where

import GHC.Stack (HasCallStack)

import Data.Either (isLeft)

import Grisette
  ( EvalSym (..)
  , EvalSym1 (..)
  , Mergeable (..)
  , Mergeable1 (..)
  , MergingStrategy (..)
  , product2Strategy
  , wrapStrategy
  )

-- | A marker which allows a non-mergeable value to simply implement no merging
-- strategy.
newtype NoMerge a where
  NoMerge :: a -> NoMerge a

instance Mergeable (NoMerge a) where
  rootStrategy = NoStrategy

instance Mergeable1 NoMerge where
  liftRootStrategy _ = NoStrategy

-- TODO: This doesn't really belong in this module... I guess we can keep it
-- here for now. Otherwise, we could call this Pantomime.Grisette.Util?
-- | A marker which allows a value that does not implement EvalSym to simply
-- not evaluate.
newtype NoEval a where
  NoEval :: a -> NoEval a

instance EvalSym (NoEval a) where
  evalSym _ _ = id

instance EvalSym1 NoEval where
  liftEvalSym _ _ _ = id

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
