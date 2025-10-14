{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Annotation
  ( Pantomime (..)
  , SymCompare (..)
  , Theory (..)
  , Pantomime' (..)
  , pantomime
  ) where

import Data.Typeable
import Data.Data
import GHC.Plugins
import Data.Bifunctor (Bifunctor(..))
import Data.Composition ((.:))
import Language.Haskell.TH qualified as TH

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

-- TODO: Not sure I like the name. This checks whether an expression whose
-- result is of type Bool is valid. That is, whether it will always return True.
data Theory where
  Theory ::
    -- TODO: Should these be a HashMap instead of a list? I guess for
    -- identifier interpretations, there could be dependency on earlier
    -- interpretations so it makes sense to have an ordering in the definition.
    -- For the other mapping, I guess it makes less sense. AFAIK, there is no
    -- ordering dependence in this case.
    { tyInterp :: [(TH.Name, TH.Name)]
    , idInterp :: [(TH.Name, TH.Name)]
    } -> Theory
  deriving (Show, Data, Typeable)

type Circuit s i o = s -> i -> (s, o)

data Pantomime' si sl ss i i' o o' where
  Pantomime' ::
    { observation' :: o -> o'
    , implementation' :: Circuit si i o
    , leakage' :: Circuit sl i i'
    , simulator' :: Circuit ss i' o'
    , projection' :: si -> (sl, ss)
    } -> Pantomime' si sl ss i i' o o'

pantomime
  :: Eq o'
  => Eq ss
  => Eq sl
  => Pantomime' si sl ss i i' o o'
  -> si
  -> i
  -> Bool
pantomime Pantomime' { .. } = do
  let c1 = bimap projection' observation' .: implementation'
  let c2 si i = do
        let (sl, ss) = projection' si
        let (sl', x) = leakage' sl i
        let (ss', o) = simulator' ss x
        ((sl', ss'), o)

  \si i -> c1 si i == c2 si i
