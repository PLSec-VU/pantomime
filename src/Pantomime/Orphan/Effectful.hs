{-# OPTIONS_GHC -Wno-orphans #-}

-- TODO: I don't really like this orphan instance. I wonder if there is anything
-- better we could do. We really only use this in one place, the 'Eval' monad.
-- Maybe we could define a newtype wrapper for Eff and then derive via a
-- coercion.
module Pantomime.Orphan.Effectful
  (
  ) where

import Grisette (EvalSym (..), EvalSym1 (..), evalSym1)

import Effectful (Eff)

instance EvalSym a => EvalSym (Eff es a) where
  evalSym = evalSym1

instance EvalSym1 (Eff es) where
  liftEvalSym f fill model = fmap $ f fill model
