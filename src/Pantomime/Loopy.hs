{-# LANGUAGE GADTs #-}

module Pantomime.Loopy
  ( Circuit (..)
  , eq
  , assocL
  , assocR
  , collapse
  , loosenL
  , loosenR
  -- , Rewrite (..)
  -- , assoc
  ) where

-- import GHC.Plugins

import Prelude hiding (id, (.))

import Control.Applicative (Alternative (..))
import Control.Arrow
import Control.Category

data Circuit i o where
  Circuit :: (i -> o) -> Circuit i o
  Seq :: Circuit i a -> Circuit a o -> Circuit i o
  Par :: Circuit i o -> Circuit i' o' -> Circuit (i, i') (o, o')
  Loop :: s -> Circuit (i, s) (o, s) -> Circuit i o

instance Category Circuit where
  id = Circuit id
  (.) = flip Seq

instance Arrow Circuit where
  arr f = Circuit f
  (***) = Par

type MonadTactic m = (Monad m, Alternative m)

eq
  :: MonadTactic m
  => Circuit i o
  -> Circuit i o
  -> m (Circuit i o)
eq goal current = do
  goal' <- combinational goal
  current' <- combinational current
  -- FIXME: This should actually check equivalence and reject the rule if it is
  -- false.
  _ <- undefined goal' current'
  pure goal

-- | Convert a 'Circuit' into a combinational function, if possible.
--
-- As the 'Loop' construct describes sequential circuitry, it cannot be
-- converted.
combinational
  :: Alternative m
  => Circuit i o
  -> m (i -> o)
combinational = \case
  Circuit circuit -> pure circuit
  Seq lhs rhs -> liftA2 (>>>) (combinational lhs) (combinational rhs)
  Par lhs rhs -> liftA2 (***) (combinational lhs) (combinational rhs)
  Loop _ _ -> empty

-- | Associate sequential composition leftways.
assocL
  :: MonadTactic m
  => Circuit i o
  -> m (Circuit i o)
assocL = \case
  Seq x (Seq y z) -> pure $ Seq (Seq x y) z
  _ -> empty

-- | Associate a sequential composition rightways. 
assocR
  :: MonadTactic m
  => Circuit i o
  -> m (Circuit i o)
assocR = \case
  Seq (Seq x y) z -> pure $ Seq x (Seq y z) 
  _ -> empty

-- | Collapse two 'Loop' circuits into a single 'Loop' over a merged state.
collapse
  :: MonadTactic m
  => Circuit i o
  -> m (Circuit i o)
collapse = \case
  Loop s1 (Loop s2 c) -> do
    let assocL' (x, (y, z)) = ((x, y), z)
    let assocR' ((x, y), z) = (x, (y, z))
    pure $ Loop (s1, s2) (arr assocL' >>> c >>> arr assocR')
  _ -> empty

-- | Loosen a loop on the left of a sequential composition over the entire
-- circuit.
loosenL
  :: MonadTactic m
  => Circuit i o
  -> m (Circuit i o)
loosenL = \case
  Seq (Loop s c1) c2 -> pure $ Loop s (c1 >>> first c2)
  _ -> empty

-- | Loosen a loop on the right of a sequential composition over the entire
-- circuit.
loosenR
  :: MonadTactic m
  => Circuit i o
  -> m (Circuit i o)
loosenR = \case
  Seq c1 (Loop s c2) -> pure $ Loop s (first c1 >>> c2)
  _ -> empty

-- data Rewrite a where
--   Rewrite ::
--     { to :: a -> Maybe a
--     , from :: a -> Maybe a
--     } -> Rewrite a

-- assoc :: Rewrite (Circuit i o)
-- assoc = Rewrite
--   { to = \case
--     Seq x (Seq y z) -> pure $ Seq (Seq x y) z
--     _ -> empty
--   , from = \case
--     Seq (Seq x y) z -> pure $ Seq x (Seq y z) 
--     _ -> empty
--   }

-- identityR :: Rewrite (Circuit i o)
-- identityR = Rewrite
--   { to = \case
--     -- TODO: Here should be a check whether i is actually the identity circuit.
--     Seq x i -> pure $ undefined
--     _ -> empty
--   , from = \x -> pure $ Seq x id
--   }

-- data Derivation a where
--   Leaf :: a -> a -> Derivation a
--   Loopy :: (i -> s -> (o, s)) -> (i -> s' -> (o, s')) -> Derivation (i -> o)


-- TODO: I don't think Circuit is an instance of ArrowLoop? Or at least, Loop is
-- not the correct construct for ArrowLoop as we want to give it some initial
-- state.
-- instance ArrowLoop Circuit where
--   loop circuit = Loop
