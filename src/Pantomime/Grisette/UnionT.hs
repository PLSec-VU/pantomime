{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingVia #-}

module Pantomime.Grisette.UnionT
  ( UnionT (..)
  , runUnionT
  ) where

import Grisette
  ( Union
  , MergingStrategy (..)
  , TryMerge (..)
  , Mergeable (..)
  , Mergeable1 (..)
  , SimpleMergeable (..)
  , SimpleMergeable1 (..)
  , SymBranching (..)
  , EvalSym (..)
  , EvalSym1 (..)
  , evalSym1
  , rootStrategy1
  , mrgIf
  , pattern Con
  )

import Data.Coerce (coerce)
import Data.Traversable (for)

import Control.Monad (join, liftM)

import Pantomime.Orphan.Grisette ()
import Control.Monad.Trans (MonadTrans (..))

-- | Union monad transformer.
--
-- For more details on the monad itself, check out the base 'Union' monad.
--
-- WARNING: This is not a valid monad transformer for most monads. The exception
-- to this rule are commutative monads (i.e. monads where 'x >> y == y >> x').
-- This excludes almost all monads. For readers familiar with the broken
-- implementation of the 'ListT' monad transformer: this is broken in exactly
-- the same way.
--
-- Why still have it if it is broken? A non broken variant (i.e. one that
-- is a valid transformer for all monads) would require the inner monad to
-- be mergeable if you actually want to do symbolic branching. This would
-- leave only an error and writer monad as sensible options. Anything that is
-- function-like (e.g. reader) is not mergeable unless the resulting value is
-- SimpleMergeable. This defeats the whole purpose of using Union in the first
-- place. (To be honest, I haven't written this alternative transformer, so
-- I'm not 100% sure if with the mergeable constraint it is possible to write a
-- non-broken one! Perhaps there is not even a good way to write it...)
--
-- The alternative we use here is the requirement of commutativity. This one
-- makes for a broken transformer, but it works for the cases we care about.
-- At the end of the day, we just want to use an 'Eff' monad with some
-- commutative algebraic effects. Ideally we ensure that indeed these effects
-- are commutative. Enforcing this is perhaps difficult though.
--
-- In fact, sometimes it is completely okay to not use a commutative effects.
-- Consider for example the error effect. The order in which computations are
-- run might affect the final error that is given. In many cases though, which
-- error is selected is not relevant, only that some error occurred.
newtype UnionT m a where
  UnionT :: UnionTC m a -> UnionT m a

runUnionT :: UnionT m a -> UnionTC m a
runUnionT = coerce

-- | Inner type of UnionT, useful for coercions.
type UnionTC m a = m (Union a)

instance Functor m => Functor (UnionT m) where
  fmap f = coerce $ fmap @m (fmap @Union f)

instance Applicative m => Applicative (UnionT m) where
  (<*>) @a @b = coerce $ liftA2 @m ((<*>) @Union @a @b)
  pure @a = coerce $ pure @m . pure @Union @a

-- TODO: I'm using an orphan implementation for Traversable on Union. Should
-- I just make a pull request for it's implementation at this point?
instance Monad m => Monad (UnionT m) where
  (>>=) @a @b = coerce go
    where
      go :: UnionTC m a -> (a -> UnionTC m b) -> UnionTC m b
      go m f = do
        union <- m
        fmap join $ for union f

instance MonadTrans UnionT where
  lift = UnionT . liftM pure

instance Functor m => TryMerge (UnionT m) where
  tryMergeWithStrategy @a = coerce $ fmap @m . tryMergeWithStrategy @Union @a

instance (Applicative m, Mergeable a) => Mergeable (UnionT m a) where
  rootStrategy = rootStrategy1

instance Applicative m => Mergeable1 (UnionT m) where
  liftRootStrategy = SimpleStrategy . mrgIfWithStrategy

instance (Applicative m, Mergeable a) => SimpleMergeable (UnionT m a) where
  mrgIte = mrgIf

instance Applicative m => SimpleMergeable1 (UnionT m) where
  liftMrgIte = mrgIfWithStrategy . SimpleStrategy

-- NOTE: Apart from the monadic instance, the symbolic branching also makes use
-- of the commutativity property. That is, monadically binding the branches in
-- either order shouldn't change the outcome as we assume that
-- 'then >> else == else >> then'.
--
-- Apart from this, we drop usages of branches that are never taken. That is,
-- 'If true then else == then' and 'If false then else == else'.
instance Applicative m => SymBranching (UnionT m) where
  mrgIfWithStrategy @a strategy scrut true false = case scrut of
    Con scrut'
      | scrut' -> tryMergeWithStrategy strategy true
      | otherwise -> tryMergeWithStrategy strategy false
    _ -> coerce go true false
    where
      go :: UnionTC m a -> UnionTC m a -> UnionTC m a
      go = liftA2 $ mrgIfWithStrategy strategy scrut

  mrgIfPropagatedStrategy @a scrut = coerce go
    where
      go :: UnionTC m a -> UnionTC m a -> UnionTC m a
      go true false = case scrut of
        Con scrut'
          | scrut' -> true
          | otherwise -> false
        _ -> liftA2 (mrgIfPropagatedStrategy scrut) true false

instance (EvalSym1 m, EvalSym a) => EvalSym (UnionT m a) where
  evalSym = evalSym1

instance EvalSym1 m => EvalSym1 (UnionT m) where
  liftEvalSym @a = coerce $ liftEvalSym @m . liftEvalSym @Union @a
