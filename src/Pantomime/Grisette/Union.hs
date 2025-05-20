{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}

module Pantomime.Grisette.Union
  ( Union (..)
  , unUnion
  ) where

import Grisette.Unified (EvalModeTag (..), BaseMonad, DecideEvalMode, withMode)
import Grisette
  ( Mergeable (..)
  , Mergeable1 (..)
  , SimpleMergeable (..)
  , SimpleMergeable1 (..)
  , SymBranching (..)
  , PlainUnion (..)
  , TryMerge (..)
  , EvalSym (..)
  , EvalSym1 (..)
  , SymEq (..)
  , SymEq1 (..)
  , ToSym (..)
  , ToSym1 (..)
  , ToCon (..)
  , ToCon1 (..)
  , GenSym (..)
  , GenSymSimple (..)
  , wrapStrategy
  , rootStrategy1
  , mrgIte1
  , mrgIf
  , evalSym1
  , symEq1
  , toSym1
  , toCon1
  )

import Data.Functor.Classes

-- | A wrapper around the Grisette 'Union' type.
--
-- The reason for the wrapper is that 'BaseMonad' from 'Grisette.Unified' is
-- hard to work with. Primarily due to many typeclass constraints that need to
-- be pulled in. Instead, we just base the typeclass instances solely on
-- 'DecideEvalMode', which simplifies constraints a ton.
newtype Union (mode :: EvalModeTag) a where
  Union :: BaseMonad mode a -> Union  mode a

-- TODO: This is not really a good way to unwrap. We should provide some other
-- methods.
-- | Gather the underlying Grisette BaseMonad.
unUnion :: Union mode a -> BaseMonad mode a
unUnion (Union m) = m

instance DecideEvalMode mode => Functor (Union mode) where
  fmap f (Union m) = do
    let fmap' = withMode @mode fmap fmap
    Union $ fmap' f m

instance DecideEvalMode mode => Applicative (Union mode) where
  pure = do
    let pure' = withMode @mode pure pure
    Union . pure'

  Union f <*> Union m = do
    let fapp = withMode @mode (<*>) (<*>)
    Union $ fapp f m

instance DecideEvalMode mode => Monad (Union mode) where
  Union m >>= f = do
    let bind = withMode @mode (>>=) (>>=)
    let f' = unUnion . f
    Union $ bind m f'

instance DecideEvalMode mode => TryMerge (Union mode) where
  tryMergeWithStrategy strategy (Union m) = do
    let op = withMode @mode tryMergeWithStrategy tryMergeWithStrategy
    Union $ op strategy m

instance (DecideEvalMode mode, Mergeable a) => Mergeable (Union mode a) where
  rootStrategy = rootStrategy1

instance DecideEvalMode mode => Mergeable1 (Union mode) where
  liftRootStrategy strategy = do
    let op = withMode @mode liftRootStrategy liftRootStrategy
    wrapStrategy (op strategy) Union unUnion

instance SimpleMergeable a => SimpleMergeable (Union C a) where
  mrgIte = mrgIte1

instance SimpleMergeable1 (Union C) where
  liftMrgIte f cond (Union tr) (Union fl) = do
    Union $ liftMrgIte f cond tr fl

instance Mergeable a => SimpleMergeable (Union S a) where
  mrgIte = mrgIf

instance SimpleMergeable1 (Union S) where
  liftMrgIte f cond (Union tr) (Union fl) = do
    Union $ liftMrgIte f cond tr fl

-- TODO: I'm not sure I understand what the purpose of this is. Identity does
-- not implement it, so we can only allow symbolic versions.
instance (forall a. Mergeable a => SimpleMergeable (Union S a))=> SymBranching (Union S) where
  mrgIfWithStrategy strategy cond (Union tr) (Union fl) = do
    Union $ mrgIfWithStrategy strategy cond tr fl

  mrgIfPropagatedStrategy cond (Union tr) (Union fl) = do
    Union $ mrgIfPropagatedStrategy cond tr fl

instance PlainUnion (Union S) where
  singleView = singleView . unUnion

  ifView = do
    let wrap (cond, tr, fl) = (cond, Union tr, Union fl)
    fmap wrap . ifView . unUnion

instance (DecideEvalMode mode, EvalSym a) => EvalSym (Union mode a) where
  evalSym = evalSym1

instance DecideEvalMode mode => EvalSym1 (Union mode) where
  liftEvalSym f fill model (Union m) = do
    let op = withMode @mode liftEvalSym liftEvalSym
    Union $ op f fill model m

instance (DecideEvalMode mode, SymEq a) => SymEq (Union mode a) where
  (.==) = symEq1

instance DecideEvalMode mode => SymEq1 (Union mode) where
  liftSymEq f (Union lhs) (Union rhs) = do
    let op = withMode @mode liftSymEq liftSymEq
    op f lhs rhs

instance (DecideEvalMode mode, Eq a) => Eq (Union mode a) where
  (==) = eq1

instance DecideEvalMode mode => Eq1 (Union mode) where
  liftEq f (Union lhs) (Union rhs) = do
    let op = withMode @mode liftEq liftEq
    op f lhs rhs

instance DecideEvalMode mode => Show (Union mode a) where
  show = withMode @mode show show

instance DecideEvalMode mode => Show1 (Union mode) where
  liftShowsPrec sp sl d (Union m) = do
    let op = withMode @mode liftShowsPrec liftShowsPrec
    op sp sl d m

instance (DecideEvalMode mode, ToSym a b) => ToSym (Union mode a) (Union S b) where
  toSym = toSym1

instance DecideEvalMode mode => ToSym1 (Union mode) (Union S) where
  liftToSym f (Union m) = do
    let op = withMode @mode liftToSym liftToSym
    Union $ op f m

instance (DecideEvalMode mode, ToCon a b) => ToCon (Union S a) (Union mode b) where
  toCon = toCon1

instance DecideEvalMode mode => ToCon1 (Union S) (Union mode) where
  liftToCon f (Union m) = do
    let op = withMode @mode liftToCon liftToCon
    Union <$> op f m

instance GenSym spec a => GenSym spec (Union S a)

instance GenSym spec a => GenSymSimple spec (Union S a) where
  simpleFresh spec = Union <$> simpleFresh spec
