{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Annotation
  ( Pantomime (..)
  , SymCompare (..)
  ) where

import Data.Typeable
import Data.Data
import GHC.Plugins

-- | Leakage specification of a circuit.
--
-- Annotation should be on a circuit of type: Circuit si i o
data Pantomime a = Pantomime
  { observation :: a
  -- ^ Observation: Circuit so o o'
  , leakage :: a
  -- ^ Leakage: Circuit sl i a
  , simulator :: a
  -- ^ Simulator: Circuit ss a o'
  , projection :: a
  -- ^ State Projection: (si, so) -> (sl, ss)
  }
  deriving (Show, Data, Typeable, Functor, Traversable, Foldable)

instance Outputable a => Outputable (Pantomime a) where
  ppr spec = text "Pantomime" $+$ nest 2 fields
    where
      fields = vcat
        [ "{" <+> ppr (observation spec)
        , "," <+> ppr (leakage spec)
        , "," <+> ppr (simulator spec)
        , "," <+> ppr (projection spec)
        , "}"
        ]

-- TODO: Maybe remove the Sym part. We should also rebrand this to a Pantomime
-- named operation perhaps?
newtype SymCompare a = SymCompare a
  deriving (Show, Data, Typeable, Functor, Traversable, Foldable)

instance Outputable a => Outputable (SymCompare a) where
  ppr (SymCompare value) = "SymCompare" <+> ppr value

