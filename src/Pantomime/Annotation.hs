module Pantomime.Annotation
  ( Theory (..)
  , Circuit
  , Pantomime (..)
  , pantomime
  ) where

import Data.Bifunctor (Bifunctor(..))
import Data.Composition ((.:))
import Data.Data (Data, Typeable)

import Pantomime.Axiom (PluginAxioms)

-- TODO: Not sure I like the name. This checks whether an expression whose
-- result is of type Bool is valid. That is, whether it will always return True.
data Theory where
  Theory :: PluginAxioms -> Theory
  deriving (Show, Data, Typeable)

type Circuit s i o = s -> i -> (s, o)

data Pantomime si sl ss i i' o o' where
  Pantomime ::
    { observation :: o -> o'
    , implementation :: Circuit si i o
    , leakage :: Circuit sl i i'
    , simulator :: Circuit ss i' o'
    , projection :: si -> (sl, ss)
    } -> Pantomime si sl ss i i' o o'

pantomime
  :: Eq o'
  => Eq ss
  => Eq sl
  => Pantomime si sl ss i i' o o'
  -> si
  -> i
  -> Bool
pantomime Pantomime { .. } = do
  let c1 = bimap projection observation .: implementation
  let c2 si i = do
        let (sl, ss) = projection si
        let (sl', x) = leakage sl i
        let (ss', o) = simulator ss x
        ((sl', ss'), o)

  \si i -> c1 si i == c2 si i
