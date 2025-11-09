{-# LANGUAGE DuplicateRecordFields #-}

module Pantomime.Annotation
  ( Theory (..)
  , Circuit

  , Pantomime (..)
  , pantomime

  , NonInterference (..)
  , tickStateCorrespondence
  , projectionCoherence
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

-- TODO: There are some duplicate record fields here. Perhaps we should change
-- this?
data NonInterference si sl ss i l o where
  NonInterference ::
    { implementation :: Circuit si i o
    , leakage :: Circuit sl i l
    , projection :: si -> (sl, ss)
    } -> NonInterference si sl ss i l o

-- TODO: The 0 and 1 naming is incredibly confusing. Ideally, users would
-- be able to write a single theory. Sadly, just adding an && between these
-- will likely be a bit slow than necessary. Also, it will be a bit harder to
-- distinguish where it failed. For now, I just separated the two checks so one
-- can query the solver twice.
--
-- Okay I gave them better names. Still, ideally this becomes one single check!
tickStateCorrespondence
  :: Eq sl
  => NonInterference si sl ss i l o
  -> si
  -> i
  -> Bool
tickStateCorrespondence NonInterference { .. } = do
  let leakage' s i = do
        let (sl, _ss) = projection s
        let (sl', _o) = leakage sl i
        sl'
  let implementation' s i = do
        let (s', _o) = implementation s i
        let (sl', _ss') = projection s'
        sl'

  \s i -> leakage' s i == implementation' s i

projectionCoherence
  :: Eq o
  => Eq l
  => Eq ss
  => NonInterference si sl ss i l o
  -> si
  -> i
  -> si
  -> i
  -> Bool
projectionCoherence NonInterference { .. } = do
  let leakage' s i = do
        let (sl, ss) = projection s
        let (_sl', o) = leakage sl i
        (ss, o)
  let implementation' s i = do
        let (s', o) = implementation s i
        let (_sl', ss') = projection s'
        (ss', o)

  \s i s' i' -> do
    let pre = leakage' s i == leakage' s' i'
    let post = implementation' s i == implementation' s' i'
    not pre || post
