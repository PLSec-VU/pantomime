{-# LANGUAGE TemplateHaskellQuotes #-}

module Pantomime.TH
  ( pantomime
  ) where

import Language.Haskell.TH qualified as TH
import Pantomime.Marker

pantomime :: TH.Name -> TH.Q TH.Exp
pantomime name = do
  let nameStr = TH.nameBase name
  pure $ TH.AppE (TH.AppE (TH.VarE 'pantomimeMarker') (TH.VarE name)) (TH.LitE (TH.StringL nameStr))

