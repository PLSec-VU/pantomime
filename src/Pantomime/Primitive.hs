{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Pantomime.Primitive
  ( Primitive (..)
  , RuntimeGenSymSimple
  ) where

import GHC.Plugins hiding (empty)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Builtin.Types.Prim
import GHC.Platform (PlatformWordSize)
import GHC.TypeLits (KnownNat)

import Grisette.SymPrim
  ( SymFP
  , SymFP32
  , SymFP64
  , ValidFP
  , SymInteger
  )
import Grisette.Unified (DecideEvalMode (..), EvalModeTag (..))
import Grisette
  ( LogicalOp (..)
  , EvalSym (..)
  , GenSymSimple (..)
  )

import Control.Monad (void)

import Effectful
import Effectful.Grisette.Fresh (Fresh)
import Effectful.Error.Static (Error, throwError_)

import Pantomime.WordSize
import Pantomime.Runtime
import Pantomime.MonadEval
import Pantomime.Grisette.BitVector

-- | Primitive values supported by the symbolic solver.
data Primitive (mode :: EvalModeTag) (ws :: PlatformWordSize) where
  -- TODO: Add support for Char
  -- Char :: RuntimeValue (SymWordN 31) -> Value m n
  -- BigNat :: RuntimeValue SymInteger -> Value m n
  Int :: RuntimeValue mode (IntPW mode ws) -> Primitive mode ws
  Int8 :: RuntimeValue mode (IntN mode 8) -> Primitive mode ws
  Int16 :: RuntimeValue mode (IntN mode 16) -> Primitive mode ws
  Int32 :: RuntimeValue mode (IntN mode 32) -> Primitive mode ws
  Int64 :: RuntimeValue mode (IntN mode 64) -> Primitive mode ws
  Word :: RuntimeValue mode (WordPW mode ws) -> Primitive mode ws
  Word8 :: RuntimeValue mode (WordN mode 8) -> Primitive mode ws
  Word16 :: RuntimeValue mode (WordN mode 16) -> Primitive mode ws
  Word32 :: RuntimeValue mode (WordN mode 32) -> Primitive mode ws
  Word64 :: RuntimeValue mode (WordN mode 64) -> Primitive mode ws
  -- TODO: Some of the primitives still need to get the proper wrapper. That is,
  -- this data type is not yet fully parametric on the eval mode, and we wrap
  -- the values different so we don't need to carry around all the dictionaries.
  Float :: RuntimeValue mode SymFP32 -> Primitive mode ws
  Double :: RuntimeValue mode SymFP64 -> Primitive mode ws
  -- ByteArray'
  --   :: RuntimeValue S (ByteArray ws)
  --   -> Primitive ws
  -- TODO: This is a really poor implementation of ByteArrays. We should change
  -- it! What might be good is an SMT solver like array with load store
  -- semantics. I.e. just remember the last x stores and loads. Not sure what to
  -- do about out-of-bounds accesses. I don't think they can be modeled well...
  ByteArray
    :: RuntimeValue mode (IntPW mode ws)
    -> RuntimeValue mode SymInteger
    -> Primitive mode ws

instance Outputable (Primitive mode ws) where
  ppr = \case
    Int _ -> "Int#"
    Int8 _ -> "Int8#"
    Int16 _ -> "Int16#"
    Int32 _ -> "Int32#"
    Int64 _ -> "Int64#"
    Word _ -> "Word#"
    Word8 _ -> "Word8#"
    Word16 _ -> "Word16#"
    Word32 _ -> "Word32#"
    Word64 _ -> "Word64#"
    Float _ -> "Float#"
    Double _ -> "Double#"
    ByteArray _ _ -> "ByteArray#"

instance (DecideEvalMode mode, KnownWordSize ws) => EvalSym (Primitive mode ws) where
  evalSym fill model = \case
    Int value -> Int $ evalSym' value
    Int8 value -> Int8 $ evalSym' value
    Int16 value -> Int16 $ evalSym' value
    Int32 value -> Int32 $ evalSym' value
    Int64 value -> Int64 $ evalSym' value
    Word value -> Word $ evalSym' value
    Word8 value -> Word8 $ evalSym' value
    Word16 value -> Word16 $ evalSym' value
    Word32 value -> Word32 $ evalSym' value
    Word64 value -> Word64 $ evalSym' value
    Float value -> Float $ evalSym' value
    Double value -> Double $ evalSym' value
    ByteArray size array -> ByteArray (evalSym' size) (evalSym' array)
    where
      evalSym' :: EvalSym a => a -> a
      evalSym' = evalSym fill model

instance DecideEvalMode mode => Forceable mode (Primitive mode ws) where
  force constraints = \case
    Int value -> Int $ force' value
    Int8 value -> Int8 $ force' value
    Int16 value -> Int16 $ force' value
    Int32 value -> Int32 $ force' value
    Int64 value -> Int64 $ force' value
    Word value -> Word $ force' value
    Word8 value -> Word8 $ force' value
    Word16 value -> Word16 $ force' value
    Word32 value -> Word32 $ force' value
    Word64 value -> Word64 $ force' value
    Float value -> Float $ force' value
    Double value -> Double $ force' value
    -- TODO: Maybe we should force the size. Not sure yet.
    ByteArray size value -> ByteArray size $ force' value
    where
      force' :: Forceable mode a => a -> a
      force' = force constraints

instance DecideEvalMode mode => Spineable mode (Primitive mode ws) where
  spine = \case
    Int value -> void value
    Int8 value -> void value
    Int16 value -> void value
    Int32 value -> void value
    Int64 value -> void value
    Word value -> void value
    Word8 value -> void value
    Word16 value -> void value
    Word32 value -> void value
    Word64 value -> void value
    Float value -> void value
    Double value -> void value
    ByteArray size value -> size >> void value

instance (Error EvalError :> es, KnownWordSize ws) => WeakEq (Eff es) (Primitive S ws) where
  weakEq = curry $ \case
    (Int lhs, Int rhs) -> weakEq lhs rhs
    (Int8 lhs, Int8 rhs) -> weakEq lhs rhs
    (Int16 lhs, Int16 rhs) -> weakEq lhs rhs
    (Int32 lhs, Int32 rhs) -> weakEq lhs rhs
    (Int64 lhs, Int64 rhs) -> weakEq lhs rhs
    (Word lhs, Word rhs) -> weakEq lhs rhs
    (Word8 lhs, Word8 rhs) -> weakEq lhs rhs
    (Word16 lhs, Word16 rhs) -> weakEq lhs rhs
    (Word32 lhs, Word32 rhs) -> weakEq lhs rhs
    (Word64 lhs, Word64 rhs) -> weakEq lhs rhs
    (Float lhs, Float rhs) -> weakEq lhs rhs
    (Double lhs, Double rhs) -> weakEq lhs rhs
    (ByteArray lsize larr, ByteArray rsize rarr) -> do
      eqSize <- weakEq lsize rsize
      eqArr <- weakEq larr rarr
      pure $ eqSize .&& eqArr
    _ -> throwError_ IllTyped

instance (Error EvalError :> es, KnownWordSize ws) => EvalIte (Eff es) (Primitive S ws) where
  evalIte cond = curry $ \case
    (Int lhs, Int rhs) -> Int <$> evalIte cond lhs rhs
    (Int8 lhs, Int8 rhs) -> Int8 <$> evalIte cond lhs rhs
    (Int16 lhs, Int16 rhs) -> Int16 <$> evalIte cond lhs rhs
    (Int32 lhs, Int32 rhs) -> Int32 <$> evalIte cond lhs rhs
    (Int64 lhs, Int64 rhs) -> Int64 <$> evalIte cond lhs rhs
    (Word lhs, Word rhs) -> Word <$> evalIte cond lhs rhs
    (Word8 lhs, Word8 rhs) -> Word8 <$> evalIte cond lhs rhs
    (Word16 lhs, Word16 rhs) -> Word16 <$> evalIte cond lhs rhs
    (Word32 lhs, Word32 rhs) -> Word32 <$> evalIte cond lhs rhs
    (Word64 lhs, Word64 rhs) -> Word64 <$> evalIte cond lhs rhs
    (Float lhs, Float rhs) -> Float <$> evalIte cond lhs rhs
    (Double lhs, Double rhs) -> Double <$> evalIte cond lhs rhs
    (ByteArray lsize larr, ByteArray rsize rarr) -> do
      size <- evalIte cond lsize rsize
      array <- evalIte cond larr rarr
      pure $ ByteArray size array
    _ -> throwError_ IllTyped

class
  ( GenSymSimple spec (RuntimeValue S SymInteger)
  , forall eb sb. ValidFP eb sb => GenSymSimple spec (RuntimeValue S (SymFP eb sb))
  , forall n. KnownNat n => GenSymSimple spec (RuntimeValue S (IntN S n))
  , forall n. KnownNat n => GenSymSimple spec (RuntimeValue S (WordN S n))
  , forall pw. KnownWordSize pw => GenSymSimple spec (RuntimeValue S (IntPW S pw))
  , forall pw. KnownWordSize pw => GenSymSimple spec (RuntimeValue S (WordPW S pw))
  ) => RuntimeGenSymSimple spec

instance
  ( GenSymSimple spec (RuntimeValue S SymInteger)
  , forall eb sb. ValidFP eb sb => GenSymSimple spec (RuntimeValue S (SymFP eb sb))
  , forall n. KnownNat n => GenSymSimple spec (RuntimeValue S (IntN S n))
  , forall n. KnownNat n => GenSymSimple spec (RuntimeValue S (WordN S n))
  , forall pw. KnownWordSize pw => GenSymSimple spec (RuntimeValue S (IntPW S pw))
  , forall pw. KnownWordSize pw => GenSymSimple spec (RuntimeValue S (WordPW S pw))
  ) => RuntimeGenSymSimple spec

instance
  ( KnownWordSize ws
  , Fresh :> es
  , Error EvalError :> es
  , RuntimeGenSymSimple spec
  ) => EvalGenSym (Eff es) (Type, spec) (Primitive S ws) where
  evalFresh (ty, spec) = if
    | ty `eqType` intPrimTy -> Int <$> simpleFresh'
    | ty `eqType` int8PrimTy -> Int8 <$> simpleFresh'
    | ty `eqType` int16PrimTy -> Int16 <$> simpleFresh'
    | ty `eqType` int32PrimTy -> Int32 <$> simpleFresh'
    | ty `eqType` int64PrimTy -> Int64 <$> simpleFresh'
    | ty `eqType` wordPrimTy -> Word <$> simpleFresh'
    | ty `eqType` word8PrimTy -> Word8 <$> simpleFresh'
    | ty `eqType` word16PrimTy -> Word16 <$> simpleFresh'
    | ty `eqType` word32PrimTy -> Word32 <$> simpleFresh'
    | ty `eqType` word64PrimTy -> Word64 <$> simpleFresh'
    | ty `eqType` floatPrimTy -> Float <$> simpleFresh'
    | ty `eqType` doublePrimTy -> Double <$> simpleFresh'
    | ty `eqType` byteArrayPrimTy -> do
      size <- simpleFresh'
      array <- simpleFresh'
      pure $ ByteArray size array
    | otherwise -> throwError_ UnsupportedExpr
    where
      -- FIXME: Not all errors are actually allowed for any value. I think we
      -- should have a specific spec that tells us this. For now though, this
      -- works well enough.
      simpleFresh' :: GenSymSimple spec a => Eff es a
      simpleFresh' = simpleFresh spec
