module Pantomime.Marker
  ( pantomimeMarker
  , pantomimeNothing
  , pantomimeJust
  ) where

pantomimeMarker :: String -> Maybe [(String, String)]
pantomimeMarker name = error $
  "The marker function 'pantomimeMarker' for '" ++ name ++ "' was not replaced by the GHC compiler plugin pass."
{-# NOINLINE pantomimeMarker #-}

pantomimeNothing :: Maybe [(String, String)]
pantomimeNothing = Nothing
{-# NOINLINE pantomimeNothing #-}

pantomimeJust :: [(String, String)] -> Maybe [(String, String)]
pantomimeJust x = Just x
{-# NOINLINE pantomimeJust #-}
