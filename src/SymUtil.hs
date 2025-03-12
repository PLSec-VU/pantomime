{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module SymUtil
  ( KnownPos
  , foldM'
  , foldM_'
  , whyFail
  ) where

import GHC.TypeLits (KnownNat, type (<=))

import Control.Monad (foldM, foldM_)
import Control.Monad.Except (MonadError (..))

type KnownPos n = (KnownNat n, 1 <= n)

-- | The usual 'foldM', but with its arguments switched.
--
-- The use for this is that one may use this to write an expression in the
-- following shape:
-- ```
-- res <- foldM' acc xs $ \acc' x -> do
--   ...
-- ```
foldM' :: (Foldable t, Monad m) => b -> t a -> (b -> a -> m b) -> m b
foldM' acc xs f = foldM f acc xs

-- | The usual 'foldM_', but with its arguments switched.
--
-- The use for this is that one may use this to write an expression in the
-- following shape:
-- ```
-- foldM'_ acc xs $ \acc' x -> do
--   ...
-- ```
foldM_' :: (Foldable t, Monad m) => b -> t a -> (b -> a -> m b) -> m ()
foldM_' acc xs f = foldM_ f acc xs

-- | Annotate why there was no result.
whyFail :: MonadError e m => e -> Maybe a -> m a
whyFail err = maybe (throwError err) pure
