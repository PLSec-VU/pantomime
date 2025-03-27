{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}

module Symbolic.Identifier
  ( Ident
  , Interpretable
  , interpretWith
  ) where

import Grisette
import Data.String (IsString(..))

import Symbolic.Runtime
import Grisette.Internal.Unified.UnifiedBV (UnifiedBVImpl(..))
import Grisette.Internal.Unified.EvalModeTag (EvalModeTag(..))

-- | Unintepreted identifier.
--
-- This may represent any abstract value, such as a function or an ADT. It is
-- meaningless unless intepretation is given to it via application of abstract
-- functions. We refer to this as a 'View'.
type Ident mode = GetWordN mode 64

type Interpretable t = Solvable (Ident C --> ConType t) (Ident S -~> t)

-- | Interpret an identifier.
--
-- To illustrate, an interpretation might be fields of a record, or how it would
-- apply as a function (i.e. assuming the Ident is like a function pointer).
interpretWith
  :: forall t
   . Mergeable t
  => Interpretable t
  => RuntimeValue S (Ident S)
  -> String
  -- TODO: I think this input String should really be Text...
  -> RuntimeValue S t
interpretWith adt name = do
  let symbol = simple . identifier . fromString $ name
  let accessor = sym symbol :: Ident S -~> t
  adt' <- adt
  mrgPure $ accessor # adt'
