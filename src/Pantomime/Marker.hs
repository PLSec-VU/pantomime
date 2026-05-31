module Pantomime.Marker
  ( pantomimeMarker
  , pantomimeNothing
  , pantomimeJust
  ) where

pantomimeMarker :: String -> Maybe String
pantomimeMarker _ = Nothing
{-# NOINLINE pantomimeMarker #-}

pantomimeNothing :: Maybe String
pantomimeNothing = Nothing
{-# NOINLINE pantomimeNothing #-}

pantomimeJust :: String -> Maybe String
pantomimeJust x = Just x
{-# NOINLINE pantomimeJust #-}
