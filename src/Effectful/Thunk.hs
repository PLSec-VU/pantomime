module Effectful.Thunk
  ( Thunkable
  , Thunk (..)
  , thunk
  , force
  , runThunkable
  ) where

import Data.Constraint (Dict (..))
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Effectful (Eff, Effect, Dispatch (..), DispatchOf, IOE, type (:>))
import Effectful.Dispatch.Static
  ( SideEffects (..)
  , StaticRep
  , evalStaticRep
  , unsafeEff_
  )

-- | Effects that can be thunked, deferring the effects to be triggered once
-- when the 'Thunk' is forced for the first time.
--
-- NOTE: This uses 'IORef' under the hood and is thus safe only in
-- single-threaded context.
data Thunkable :: Effect

type instance DispatchOf Thunkable = Static WithSideEffects

data instance StaticRep Thunkable = Thunkable

-- | A thunk contains either a plain value, or a computation that produces such
-- a plain value.
--
-- It will only run the computation the first time this value is forced: the
-- result is shared on subsequent calls and its effects are not triggered again.
newtype Thunk es a where
  Thunk :: IORef (Either a (Eff es a)) -> Thunk es a

-- | Defer the effects of a computation until it is forced.
thunk :: forall es a. Thunkable :> es => Eff es a -> Eff es (Thunk es a)
thunk m = do
  -- NOTE: We don't actually store anything in the effect stack: it exists
  -- solely to capture whether we are allowed to perform this effect. We use it
  -- here to avoid "unused constraint" warnings.
  let _ = Dict @(Thunkable :> es)
  ref <- unsafeEff_ $ newIORef (Right m)
  pure $ Thunk ref

-- | Collect the result of a computation.
--
-- This will force the effects of the operation if and only if it was not
-- triggered before.
force :: forall es a. Thunkable :> es => Thunk es a -> Eff es a
force (Thunk ref) = do
  -- NOTE: We don't actually store anything in the effect stack: it exists
  -- solely to capture whether we are allowed to perform this effect. We use it
  -- here to avoid "unused constraint" warnings.
  let _ = Dict @(Thunkable :> es)
  result <- unsafeEff_ $ readIORef ref
  case result of
    Left value -> pure value
    Right operation -> do
      value <- operation
      unsafeEff_ $ writeIORef ref (Left value)
      pure value

-- | Allows effectful computation to be thunked.
runThunkable :: IOE :> es => Eff (Thunkable : es) a -> Eff es a
runThunkable = evalStaticRep Thunkable
