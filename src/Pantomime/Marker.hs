{-# LANGUAGE FunctionalDependencies #-}

module Pantomime.Marker
  ( pantomimeMarker
  , pantomimeNothing
  , pantomimeJust
  , PantomimeType (..)
  ) where

import Pantomime.BuiltIn qualified as Pantomime

pantomimeMarker :: String -> Maybe res
pantomimeMarker name = error $
  "The marker function 'pantomimeMarker' for '" ++ name ++ "' was not replaced by the GHC compiler plugin pass."
{-# NOINLINE pantomimeMarker #-}

pantomimeNothing :: Maybe res
pantomimeNothing = Nothing
{-# NOINLINE pantomimeNothing #-}

pantomimeJust :: res -> Maybe res
pantomimeJust x = Just x
{-# NOINLINE pantomimeJust #-}

class PantomimeType assertion res | assertion -> res where
  pantomimeMarker' :: assertion -> String -> Maybe res
  pantomimeMarker' _ name = pantomimeMarker name
  {-# NOINLINE pantomimeMarker' #-}

instance PantomimeType Pantomime.Bool ()
instance PantomimeType (a -> Pantomime.Bool) a
instance PantomimeType (a -> b -> Pantomime.Bool) (a, b)
instance PantomimeType (a -> b -> c -> Pantomime.Bool) (a, b, c)
instance PantomimeType (a -> b -> c -> d -> Pantomime.Bool) (a, b, c, d)
instance PantomimeType (a -> b -> c -> d -> e -> Pantomime.Bool) (a, b, c, d, e)
instance PantomimeType (a -> b -> c -> d -> e -> f -> Pantomime.Bool) (a, b, c, d, e, f)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> Pantomime.Bool) (a, b, c, d, e, f, g)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> Pantomime.Bool) (a, b, c, d, e, f, g, h)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> i -> Pantomime.Bool) (a, b, c, d, e, f, g, h, i)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> Pantomime.Bool) (a, b, c, d, e, f, g, h, i, j)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> Pantomime.Bool) (a, b, c, d, e, f, g, h, i, j, k)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> Pantomime.Bool) (a, b, c, d, e, f, g, h, i, j, k, l)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> Pantomime.Bool) (a, b, c, d, e, f, g, h, i, j, k, l, m)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> Pantomime.Bool) (a, b, c, d, e, f, g, h, i, j, k, l, m, n)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> Pantomime.Bool) (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> Pantomime.Bool) (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> q -> Pantomime.Bool) (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> q -> r -> Pantomime.Bool) (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> q -> r -> s -> Pantomime.Bool) (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s)
instance PantomimeType (a -> b -> c -> d -> e -> f -> g -> h -> i -> j -> k -> l -> m -> n -> o -> p -> q -> r -> s -> t -> Pantomime.Bool) (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t)

