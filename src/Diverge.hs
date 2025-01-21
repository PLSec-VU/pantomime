{-# OPTIONS_GHC -fno-warn-orphans #-}

module Diverge
  ( diverge
  ) where

-- | Diverging code snippet.
--
-- This should never be used in actual code. It is a marker used inside of the
-- rewriter to improve confluence. This marker helps us identify which code
-- snippets diverge which allows for additional rewrites. 
--
-- A non-exhaustive list of rewrites we can do when we identify non-diverging
-- code:
-- - case diverge of { .. } -> diverge
-- - diverge x -> diverge
--
-- One can mark any code divergent by adding a RULE from the diverging snippet
-- to this function.
{-# NOINLINE diverge #-}
diverge :: a
diverge = error "diverging code rewrite, should not occur in actual code"

-- Notice that we disable the rules for common usage. We will force their usage
-- in the plugin.
{-# RULES
"error/diverge" [~]
  forall m. error m = diverge

"undefined/diverge" [~]
  undefined = diverge

"diverge x" [~]
  forall x. diverge x = diverge
#-}
