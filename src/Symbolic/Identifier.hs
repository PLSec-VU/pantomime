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
  , View
  , SolvableIdent
  -- , ReqTest
  -- , Symbolise (..)
  -- , Unary (..)
  , interpretWith
  ) where

import Grisette
import Data.String (IsString(..))

import Symbolic.Runtime
import Grisette.Internal.Unified.UnifiedBV (UnifiedBVImpl(..))
import Grisette.Internal.Unified.EvalModeTag (EvalModeTag(..))

-- import Symbolic.WordSize
import Grisette.Internal.SymPrim.Prim.Term (SupportedNonFuncPrim)
import Data.Data (Typeable)
import Data.Hashable (Hashable)

-- | Unintepreted identifier.
--
-- This may represent any abstract value, such as a function or an ADT. It is
-- meaningless unless intepretation is given to it via application of abstract
-- functions. We refer to this as a 'View'.
type Ident mode = GetWordN mode 64

-- | A view into an identifier.
--
-- To illustrate, a view might be fields of a record, or how it would apply as
-- a function (i.e. assuming the Ident is like a function pointer). 
--
-- A view is intended as a resolution of 'sym' from the 'Solvable' typeclass.
-- We cannot use the typeclass constraint due to overlapping instances. As such,
-- we require this to be resolved by the caller explicitly by manually passing
-- the instance.
--
-- TODO: Users can literally pas in any function now. We do ideally want an
-- instance of Solvable, but cannot really resolve it. Is there some way to
-- wrap an instance?
type View t = Symbol -> Ident S -~> t

class
  ( Show c
  , Hashable c
  , Typeable c
  , SupportedNonFuncPrim c
  , LinkedRep c t
  , Solvable (Ident C --> c) (Ident S -~> t)
  ) => SolvableIdent c t | t -> c where

instance
  ( Show c
  , Hashable c
  , Typeable c
  , SupportedNonFuncPrim c
  , LinkedRep c t
  ) => SolvableIdent c t where

-- | Interpret the identifier with some 'View'.
interpretWith
  :: forall t
   . Mergeable t
  => SolvableIdent (ConType t) t
  => RuntimeValue S (Ident S)
  -> String
  -- TODO: I think this input String should really be Text...
  -> RuntimeValue S t
interpretWith adt name = do
  let symbol = simple . identifier . fromString $ name
  let accessor = sym symbol :: Ident S -~> t
  adt' <- adt
  mrgPure $ accessor # adt'
