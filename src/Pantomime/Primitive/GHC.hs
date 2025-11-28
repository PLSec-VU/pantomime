-- TODO: I'm not sure about this module name. It looks as though it's about
-- GHC primitives. In reality, we just lookup all the GHC information before we
-- can perform the interpretations. I think we will at some point remove all
-- bindings of base. For this reason, perhaps 'Builtin' might be a good name for
-- this module.
{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Primitive.GHC
  ( Types (..)
  , getTypes

  , ReifyMismatch (..)
  , reifiedUnsafeRefl
  , reifiedBitVector

  , thNameToTyCon
  , thNameToId
  ) where

import Language.Haskell.TH qualified as TH

import GHC.Tc.Utils.TcType (eqType)
import GHC.Core.TyCo.Rep (UnivCoProvenance(..))
import GHC.Plugins
  ( TyCon
  , Name
  , Var
  , Id
  , Outputable (..)
  , IsLine (..)
  , GhcException (..)
  , IsDoc (..)
  , Type
  , InlinePragma (..)
  , InlineSpec (..)
  , Role (..)
  , varType
  , prettyCallStackDoc
  , callStackDoc
  , idInlinePragma
  , mkUnivCo
  )

import Pantomime.Expr (Eval, EvalExpr, failWithE)
import Pantomime.Grisette.SomeBV (SomeBV(..))
import Pantomime.Grisette.SizedBV
  ( SizedBV (..)
  , sizedBVResize
  , sizedBVResizeZ
  , sizedBVResizeS
  )
import Pantomime.Grisette.BitVector (WordN, IntN)
import Pantomime.Primitive.Operation qualified as Primitive
import Pantomime.Primitive.BitVector qualified as BitVector
import Pantomime.Primitive.BitVector (BitVector)
import Pantomime.Primitive.Reify
import Pantomime.Dict
  ( SomeNat' (..)
  , Dict (..)
  , leqNat
  , typeAdd
  , typeSub
  , someTyNat
  , unsafeDict
  )

import Data.Bits (Bits(..))
import Data.Typeable (type (:~:) (..), eqT, Proxy (..))

import Control.Monad (unless, (>=>))

import Unsafe.Coerce (unsafeEqualityProof)

import GHC.TypeNats
  ( type (+)
  , type (<=)
  , KnownNat
  , SomeNat (..)
  , someNatVal
  , natVal
  )

import Effectful
import Effectful.Error.Static
import Effectful.GHC.TH
import Effectful.GHC.TyThing
import Effectful.Exception (throwIO)
import Effectful.GHC.External

import Grisette.Unified (EvalModeTag (..))
import Grisette
  ( SymBool
  , SymEq (..)
  , SymOrd (..)
  , ToCon (..)
  , SymShift (..)
  , SymRotate (..)
  , BitCast (..)
  )

thNameToTyCon
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => TH.Name
  -> Eff es TyCon
thNameToTyCon th = do
  name <- thNameToGhcName th
  lookupTyCon name

thNameToId
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => TH.Name
  -> Eff es Id
thNameToId th = do
  name <- thNameToGhcName th
  lookupId name

data Types where
  Types ::
    { tcBitVector :: TyCon
    , tcInteger :: TyCon
    } -> Types

getTypes
  :: HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Eff es Types
getTypes = do
  tcBitVector <- thNameToTyCon ''BitVector
  tcInteger <- thNameToTyCon ''Primitive.Integer
  pure Types { .. }

data ReifyMismatch where
  ReifyMismatch
    :: Var
    -- ^ Variable to interpret.
    -> Type
    -- ^ Type of reified interpretation.
    -> ReifyMismatch

instance Outputable ReifyMismatch where
  ppr (ReifyMismatch var ty) = vcat
    [ "Variable does not have the same type as the reified interpretation."
    , "original var:" <+> ppr var <+> "::" <+> ppr (varType var)
    , "reified type:" <+> ppr ty
    ]

data Interpretation es where
  Interpretation
    :: Reify a
    => TH.Name
    -> Eval es (InterpRep es a)
    -> Interpretation es

lookupReify
  :: forall a es fs
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error ReifyMismatch :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Error () :> fs
  => HasFamInstEnvs :> fs
  => Reify a
  => TH.Name
  -> Eval fs (InterpRep fs a)
  -> Eff es (Var, EvalExpr fs)
lookupReify name interp = do
  -- Lookup the identifier.
  var <- thNameToId name

  case inl_inline $ idInlinePragma var of
    Opaque {} -> pure ()
    NoInline {} -> pure ()
    -- TODO: I should throw a proper error that says it's bad to extend
    -- inlineable functions as they are fragile when being interpreted.
    _ -> undefined

  -- Lookup the type info for reification.
  ty <- coreType @a

  -- Ensure that the interpretation has a proper reified type.
  unless (eqType ty $ varType var) do
    throwError_ $ ReifyMismatch var ty

  -- Get the expression reified from the intepretation.
  let expr = reify @a ty interp
  pure (var, expr)

lookupReifyMany
  :: forall f es fs
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error ReifyMismatch :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Error () :> fs
  => HasFamInstEnvs :> fs
  => Traversable f
  => f (Interpretation fs)
  -> Eff es (f (Var, EvalExpr fs))
lookupReifyMany = traverse \(Interpretation @r name interp) -> do
  lookupReify @r name interp

type UnsafeEqProof
  =  RTyVar_ 0
  +> RTyVar 1 (RTyVar_ 0)
  +> RTyVar 2 (RTyVar_ 0)
  +> RUnsafeEquality (RTyVar_ 0) (RTyVar 1 (RTyVar_ 0)) (RTyVar 2 (RTyVar_ 0 ))

reifiedUnsafeRefl
  :: forall es fs
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Error () :> fs
  => HasFamInstEnvs :> fs
  => Eff es (Var, EvalExpr fs)
reifiedUnsafeRefl = staticReifyError do
  lookupReify @UnsafeEqProof 'unsafeEqualityProof $ liftF3 \_k tyL tyR -> do
    let prov = PluginProv "pantomime reified 'unsafeEqualityProof'"
    pure $ mkUnivCo prov Nominal tyR tyL

type NatTv n = RTyVar n RNatural

type AlphaNat = NatTv 0

type WithNatBitVector
  =  NatTv 0
  +> RTyVar_ 1
  +> RBitVector (NatTv 0)
  ~> (RKnownNat (NatTv 0) ~> RTyVar_ 1)
  ~> RTyVar_ 1

type FromIntegerBitVector
  =  AlphaNat
  +> RKnownNat AlphaNat
  ~> RInteger
  ~> RBitVector AlphaNat

type ToIntegerBitVector
  =  AlphaNat
  +> RBitVector AlphaNat
  ~> RInteger

type UnaryBitVector
  =  AlphaNat
  +> RBitVector AlphaNat
  ~> RBitVector AlphaNat

type BinaryBitVector
  =  AlphaNat
  +> RBitVector AlphaNat
  ~> RBitVector AlphaNat
  ~> RBitVector AlphaNat

type CmpBitVector
  =  AlphaNat
  +> RBitVector AlphaNat
  ~> RBitVector AlphaNat
  ~> RBool

type ShiftBitVector n
  =  AlphaNat
  +> RBitVector AlphaNat
  ~> RInt n
  ~> RBitVector AlphaNat

type ConcatBitVector
  =  NatTv 0
  +> NatTv 1
  +> RBitVector (NatTv 0)
  ~> RBitVector (NatTv 1)
  ~> RBitVector (RAdd (NatTv 0) (NatTv 1))

type ExtBitVector
  =  NatTv 0
  +> NatTv 1
  +> RKnownNat (NatTv 1)
  ~> RLEq (NatTv 0) (NatTv 1)
  ~> RBitVector (NatTv 0)
  ~> RBitVector (NatTv 1)

type SelBitVector
  =  NatTv 0
  +> NatTv 1
  +> NatTv 2
  +> RKnownNat (NatTv 0)
  ~> RKnownNat (NatTv 1)
  ~> RLEq (RAdd (NatTv 0) (NatTv 1)) (NatTv 2)
  ~> RBitVector (NatTv 2)
  ~> RBitVector (NatTv 1)

-- :: forall upper top idx
--  . KnownNat upper
-- => KnownNat idx
-- => BitVector (upper + 1 + top)
-- -> BitVector (upper + 1 - idx)
type SlcBitVector
  =  NatTv 0
  +> NatTv 1
  +> NatTv 2
  +> RKnownNat (NatTv 0)
  ~> RKnownNat (NatTv 2)
  ~> RBitVector (RAdd (RAdd (NatTv 0) (RTyNat 1)) (NatTv 1))
  ~> RBitVector (RSub (RAdd (NatTv 0) (RTyNat 1)) (NatTv 2))

type MBndBitVector
  =  NatTv 0
  +> RBitVector (NatTv 0)

type ResBitVector
  =  NatTv 0
  +> NatTv 1
  +> RKnownNat (NatTv 1)
  ~> RBitVector (NatTv 0)
  ~> RBitVector (NatTv 1)

-- TODO: Clean up this code! It works for now though...
reifiedBitVector
  :: forall es fs
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Error () :> fs
  => HasFamInstEnvs :> fs
  => Eff es [(Var, EvalExpr fs)]
reifiedBitVector = staticReifyError $ lookupReifyMany
  [ binary 'BitVector.add (+)
  , binary 'BitVector.mul (*)
  , unary 'BitVector.abs abs
  , unary 'BitVector.signum signum
  , unary 'BitVector.negate negate
  , fromI 'BitVector.fromInteger
  , toI 'BitVector.toInteger
  , cmp 'BitVector.eq (.==)
  , cmp 'BitVector.leZ (.<=)
  , cmp 'BitVector.leS leS
  , binary 'BitVector.and (.&.)
  , binary 'BitVector.or (.|.)
  , binary 'BitVector.xor xor
  , unary 'BitVector.complement complement
  , shft 'BitVector.shiftL symShift
  , shft 'BitVector.shiftRL symShiftNegated
  -- TODO: Add arithmetic shift!
  , shft 'BitVector.shiftRA undefined
  , shft 'BitVector.rotateL symRotate
  , shft 'BitVector.rotateRL symRotateNegated
  -- TODO: Add arithmetic rotate!
  , shft 'BitVector.rotateRA undefined
  , conc 'BitVector.concat
  , ext 'BitVector.extendZ sizedBVExtZ
  , ext 'BitVector.extendS sizedBVExtS
  , sel 'BitVector.select
  , res 'BitVector.resizeZ sizedBVResizeZ
  , res 'BitVector.resizeS sizedBVResizeS
  , withN 'BitVector.withNat

  -- TODO: I want to nuke these one at some point!
  , slc 'BitVector.stupidSlice
  , bnd 'BitVector.stupidMinBound
  ]
  where
    leS :: forall n. KnownNat n => WordN S n -> WordN S n -> SymBool
    leS x y = bitCast @_ @(IntN S n) x .<= bitCast y

    withN
      :: TH.Name
      -> Interpretation fs
    withN name = Interpretation @WithNatBitVector name $ liftF4 \_n _a x f -> do
      f' <- f
      let x' = (\(SomeBV @n _) -> symbolicKnownNat @n) <$> x
      f' x'

    fromI
      :: TH.Name
      -> Interpretation fs
    fromI name = Interpretation @FromIntegerBitVector name $ liftF3 \_n c i -> do
      -- Use the concrete natural for a KnownNat constraint.
      SomeNat @n _ <- c >>= concreteKnownNat
      i >>= \case
        Left (SomeBV @m value) -> pure . SomeBV . sizedBVResize @_ @m @n $ bitCast value
        Right _ -> undefined

    toI
      :: TH.Name
      -> Interpretation fs
    toI name = Interpretation @ToIntegerBitVector name $ liftF2 \_n x -> do
      -- Use the concrete natural for a KnownNat constraint.
      -- SomeNat @n _ <- c >>= concreteKnownNat
      SomeBV x' <- x
      -- FIXME: Use proper platform size!
      -- FIXME: We should convert to a big integer when out of bounds!
      pure . Left . SomeBV @64 . bitCast . sizedBVResize @_ @_ @64 $ x'
      -- case leqNat @n @64 of
      --   Just Dict -> pure . Left . SomeBV . sizedBVResize @_ @n @64 $ x'
      --   Nothing -> undefined
      -- i >>= \case
      --   Left (SomeBV @m value) -> pure . SomeBV . sizedBVResize @_ @m @n $ bitCast value
      --   Right _ -> undefined

    binary
      :: TH.Name
      -> (forall n. KnownNat n => WordN S n -> WordN S n -> WordN S n)
      -> Interpretation fs
    binary name op = Interpretation @BinaryBitVector name $ liftF3 \_n x y -> do
      -- TODO: Should we check that the KnownNat is indeed equal to the size of
      -- the bitvector? If yes, we should do this for all other operations as
      -- well!
      SomeBV @n x' <- x
      SomeBV @m y' <- y
      Refl <- failWithE () $ eqT @n @m
      pure . SomeBV $ op x' y'

    unary
      :: TH.Name
      -> (forall n. KnownNat n => WordN S n -> WordN S n)
      -> Interpretation fs
    unary name op = Interpretation @UnaryBitVector name $ liftF2 \_n x -> do
      SomeBV x' <- x
      pure . SomeBV $ op x'

    cmp
      :: TH.Name
      -> (forall n. KnownNat n => WordN S n -> WordN S n -> SymBool)
      -> Interpretation fs
    cmp name op = Interpretation @CmpBitVector name $ liftF3 \_n x y -> do
      SomeBV @n x' <- x
      SomeBV @m y' <- y
      Refl <- failWithE () $ eqT @n @m
      pure $ op x' y'

    shft
      :: TH.Name
      -> (forall n. KnownNat n => WordN S n -> WordN S n -> WordN S n)
      -> Interpretation fs
    -- FIXME: Add proper platform size!
    shft name op = Interpretation @(ShiftBitVector 64) name $ liftF3 \_n x idx -> do
      SomeBV @n x' <- x
      idx' <- bitCast . sizedBVResize @_ @_ @n <$> idx
      pure . SomeBV $ op x' idx'

    conc
      :: TH.Name
      -> Interpretation fs
    conc name = Interpretation @ConcatBitVector name $ liftF4 \_l _r x y -> do
      SomeBV @l x' <- x
      SomeBV @r y' <- y
      let result = sizedBVConcat x' y'
      -- TODO: I don't particularly like this typeAdd thing. We should see if
      -- we could clean this up slightly!
      SomeNat' <- pure $ typeAdd @l @r
      pure $ SomeBV result

    ext
      :: TH.Name
      -> (forall l r. KnownNat l => KnownNat r => l <= r => WordN S l -> WordN S r)
      -> Interpretation fs
    ext name op = Interpretation @ExtBitVector name $ liftF5 \_l _r cr cle x -> do
      SomeNat @r _ <- cr >>= concreteKnownNat
      _ <- cle
      SomeBV @l x' <- x
      -- TODO: Clean up the dict stuff!
      Dict <- failWithE () $ leqNat @l @r
      pure . SomeBV @r $ op x'

    sel
      :: TH.Name
      -> Interpretation fs
    sel name = Interpretation @SelBitVector name $ liftF7 \_i _w _n ci cw cle x -> do
      SomeNat @idx _ <- ci >>= concreteKnownNat
      SomeNat @width _ <- cw >>= concreteKnownNat
      _ <- cle
      SomeBV @n x' <- x
      SomeNat' @sum <- pure $ typeAdd @idx @width
      Dict <- failWithE () $ leqNat @sum @n
      pure . SomeBV $ sizedBVSelect @_ @idx @width x'

    res
      :: TH.Name
      -> (forall l r. KnownNat l => KnownNat r => WordN S l -> WordN S r)
      -> Interpretation fs
    res name op = Interpretation @ResBitVector name $ liftF4 \_l _r cr x -> do
      SomeNat @r _ <- cr >>= concreteKnownNat
      SomeBV x' <- x
      pure . SomeBV @r $ op x'

    slc
      :: TH.Name
      -> Interpretation fs
    slc name = Interpretation @SlcBitVector name $ liftF6 \_u _t _i cu ci x -> do
      SomeNat @upper _ <- cu >>= concreteKnownNat
      SomeNat @idx _ <- ci >>= concreteKnownNat

      SomeNat' @upper1 <- pure $ typeAdd @upper @1
      SomeNat' @width <- pure $ typeSub @upper1 @idx

      SomeBV @n x' <- x

      -- Is this actually true?
      Dict <- pure $ unsafeDict @(idx + width <= n)

      pure . SomeBV $ sizedBVSelect @_ @idx @width x'

    bnd
      :: TH.Name
      -> Interpretation fs
    bnd name = Interpretation @MBndBitVector name $ pure \n -> do
      SomeNat @n _ <- failWithE () $ someTyNat n
      pure $ SomeBV @n 0

concreteKnownNat
  :: Error () :> es
  => Either (SomeBV (WordN S)) ()
  -> Eval es SomeNat
concreteKnownNat value = do
  nat <- case value of
    Left (SomeBV @n value') -> do
      concrete <- failWithE () $ toCon @_ @(WordN C n) value'
      pure $ fromIntegral concrete
    Right _ -> undefined

  pure $ someNatVal nat

symbolicKnownNat
  :: forall n
   . KnownNat n
  => Either (SomeBV (WordN S)) ()
symbolicKnownNat = do
  let value = natVal @n Proxy
  -- FIXME: Add in proper platform size!
  let upper = fromIntegral $ maxBound @(WordN C 64)
  if
    -- FIXME: Add in proper platform size!
    | value < upper -> Left . SomeBV @64 $ fromIntegral value
    | otherwise -> undefined

-- | Helper function to catch ReifyMismatch for constant interpretations that
-- should never fail in the first place.
staticReifyError
  :: HasCallStack
  => Eff (Error ReifyMismatch : es) a
  -> Eff es a
staticReifyError = runError >=> \case
  Right value -> pure value
  Left (cs, err) -> throwIO $ PprPanic "staticReifyError" $ vcat
    -- TODO: Should I really attach both callstacks? I'm not sure what is
    -- best as I'm rethrowing an error...
    [ ppr err
    , prettyCallStackDoc cs
    , callStackDoc
    ]
