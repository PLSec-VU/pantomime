-- TODO: I'm not sure about this module name. It looks as though it's about
-- GHC primitives. In reality, we just lookup all the GHC information before we
-- can perform the interpretations. I think we will at some point remove all
-- bindings of base. For this reason, perhaps 'Builtin' might be a good name for
-- this module.
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Primitive.GHC
  ( Types (..)
  , getTypes

  , ReifyMismatch (..)
  , reifiedIntN

  , thNameToTyCon
  , thNameToId

  -- , Operation
  -- , NumOps (..)

  -- , IntNOps (..)
  -- , getIntNOps

  -- , IntegerOps (..)
  -- , getIntegerOps

  -- , Operations (..)
  -- , getOperations
  ) where

import Language.Haskell.TH qualified as TH

import GHC.Tc.Utils.TcType (eqType)
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
  , varType
  , prettyCallStackDoc
  , callStackDoc
  , idInlinePragma
  )

import Pantomime.Expr (Eval, EvalExpr, failWithE)
import Pantomime.Grisette.SomeBV (SomeBV(..))
import Pantomime.Grisette.BitVector (IntN, WordN)
import Pantomime.Primitive.Operation qualified as Primitive
import Pantomime.Primitive.Reify
import Pantomime.Result (type (!>))

import Data.Typeable (type (:~:) (..), eqT)

import Control.Monad (unless, (>=>))

import GHC.TypeNats (KnownNat, SomeNat (..), someNatVal)

import Effectful
import Effectful.Error.Static
import Effectful.GHC.TH
import Effectful.GHC.TyThing
import Effectful.Exception (throwIO)

import Grisette.Unified (EvalModeTag (..))
import Grisette (SymBool, SymEq (..), SymOrd (..), ToCon (..))
import Pantomime.Grisette.SizedBV (sizedBVResize)
import Data.Bits (Bits(..))

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
    { tcIntN :: TyCon
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
  tcIntN <- thNameToTyCon ''Primitive.IntN
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
  => () !> fs
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
  => () !> fs
  => Traversable f
  => f (Interpretation fs)
  -> Eff es (f (Var, EvalExpr fs))
lookupReifyMany = traverse \(Interpretation @r name interp) -> do
  lookupReify @r name interp

type AlphaNat = RTyVar 0 RNatural

type UnaryIntN
  =  AlphaNat
  +> RKnownNat AlphaNat
  ~> RIntN AlphaNat
  ~> RIntN AlphaNat

type BinaryIntN
  =  AlphaNat
  +> RKnownNat AlphaNat
  ~> RIntN AlphaNat
  ~> RIntN AlphaNat
  ~> RIntN AlphaNat

type EqIntN
  =  AlphaNat
  +> RIntN AlphaNat
  ~> RIntN AlphaNat
  ~> RBool

type CmpIntN
  =  AlphaNat
  +> RKnownNat AlphaNat
  ~> RIntN AlphaNat
  ~> RIntN AlphaNat
  ~> RBool

type FromIntegerIntN
  =  AlphaNat
  +> RKnownNat AlphaNat
  ~> RInteger
  ~> RIntN AlphaNat

reifiedIntN
  :: forall es fs
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => () !> fs
  => Eff es [(Var, EvalExpr fs)]
reifiedIntN = staticReifyError $ lookupReifyMany
  [ binary 'Primitive.plusIntN (+)
  , binary 'Primitive.timesIntN (*)
  , unary 'Primitive.absIntN abs
  , unary 'Primitive.signumIntN signum
  , unary 'Primitive.negateIntN negate
  , fromI 'Primitive.fromIntegerIntN
  , eq 'Primitive.eqIntN (.==)
  , cmp 'Primitive.leIntN (.<=)
  , binary 'Primitive.andIntN (.&.)
  , binary 'Primitive.orIntN (.|.)
  , binary 'Primitive.xorIntN xor
  , unary 'Primitive.complementIntN complement
  -- , undefined 'Primitive.shiftLIntN
  -- , undefined 'Primitive.shiftRIntN
  -- , undefined 'Primitive.rotateLIntN
  -- , undefined 'Primitive.rotateRIntN
  -- , undefined 'Primitive.sizedBVConcatIntN
  -- , undefined 'Primitive.sizedBVExtZIntN
  -- , undefined 'Primitive.sizedBVExtSIntN
  -- , undefined 'Primitive.sizedBVExtIntN
  -- , undefined 'Primitive.sizedBVSelectIntN
  ]
  where
    fromI
      :: TH.Name
      -> Interpretation fs
    fromI name = Interpretation @FromIntegerIntN name $ liftF3 \_n c i -> do
      -- Convert the symbolic KnownNat constraint into a concrete Natural, if
      -- possible.
      nat <- c >>= \case
        Left (SomeBV @n value) -> do
          concrete <- failWithE () $ toCon @_ @(WordN C n) value
          pure $ fromIntegral concrete
        Right _ -> undefined

      -- Use the concrete natural for a KnownNat constraint.
      SomeNat @n _ <- pure $ someNatVal nat
      i >>= \case
        Left (SomeBV value) -> pure $ SomeBV @n (sizedBVResize value)
        Right _ -> undefined

    binary
      :: TH.Name
      -> (forall n. KnownNat n => IntN S n -> IntN S n -> IntN S n)
      -> Interpretation fs
    binary name op = Interpretation @BinaryIntN name $ liftF4 \_n c x y -> do
      _ <- c
      -- TODO: Should we check that the KnownNat is indeed equal to the size of
      -- the bitvector? If yes, we should do this for all other operations as
      -- well!
      SomeBV @n x' <- x
      SomeBV @m y' <- y
      Refl <- failWithE () $ eqT @n @m
      pure . SomeBV $ op x' y'

    unary
      :: TH.Name
      -> (forall n. KnownNat n => IntN S n -> IntN S n)
      -> Interpretation fs
    unary name op = Interpretation @UnaryIntN name $ liftF3 \_n c x -> do
      _ <- c
      SomeBV x' <- x
      pure . SomeBV $ op x'

    eq
      :: TH.Name
      -> (forall n. KnownNat n => IntN S n -> IntN S n -> SymBool)
      -> Interpretation fs
    eq name op = Interpretation @EqIntN name $ liftF3 \_n x y -> do
      SomeBV @n x' <- x
      SomeBV @m y' <- y
      Refl <- failWithE () $ eqT @n @m
      pure $ op x' y'

    cmp
      :: TH.Name
      -> (forall n. KnownNat n => IntN S n -> IntN S n -> SymBool)
      -> Interpretation fs
    cmp name op = Interpretation @CmpIntN name $ liftF4 \_n c x y -> do
      _ <- c
      SomeBV @n x' <- x
      SomeBV @m y' <- y
      Refl <- failWithE () $ eqT @n @m
      pure $ op x' y'

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

-- data Operation where
--   Operation
--     :: Typeable a
--     => Var
--     -> TypeInfo a
--     -> Operation

-- getOperation
--   :: forall a es
--    . HasCallStack
--   => Typeable a
--   => Reify a
--   => Error (LookupError TH.Name) :> es
--   => Error (LookupError Name) :> es
--   => Error ReifyMismatch :> es
--   => HasThings :> es
--   => THNameToGHCName :> es
--   => TH.Name
--   -> Eff es Operation
-- getOperation name = do
--   -- Lookup the identifier.
--   var <- thNameToId name

--   -- Lookup the type info for reification.
--   info <- typeInfo @a

--   -- Ensure that the interpretation has a proper reified type.
--   let reifyTy = reifiedTy info
--   unless (eqType reifyTy $ varType var) do
--     throwError_ $ ReifyMismatch var reifyTy

--   pure $ Operation var info

-- data NumOps where
--   NumOps ::
--     { opAdd :: Operation
--     , opMul :: Operation
--     , opAbs :: Operation
--     , opSignum :: Operation
--     , opNegate :: Operation
--     , opFromInteger :: Operation
--     } -> NumOps

-- data IntNOps where
--   IntNOps ::
--     { numIntN :: NumOps
--     } -> IntNOps

-- type FromIntegerIntN
--   =  AlphaNat
--   +> RKnownNat AlphaNat
--   ~> RInteger
--   ~> RIntN AlphaNat

-- getIntNOps
--   :: HasCallStack
--   => Error (LookupError TH.Name) :> es
--   => Error (LookupError Name) :> es
--   => Error ReifyMismatch :> es
--   => HasThings :> es
--   => THNameToGHCName :> es
--   => Eff es IntNOps
-- getIntNOps = do
--   opAdd <- getOperation @BinaryIntN 'Primitive.plusIntN
--   opMul <- getOperation @BinaryIntN 'Primitive.timesIntN
--   opAbs <- getOperation @UnaryIntN 'Primitive.absIntN
--   opSignum <- getOperation @UnaryIntN 'Primitive.signumIntN
--   opNegate <- getOperation @UnaryIntN 'Primitive.negateIntN
--   opFromInteger <- getOperation @FromIntegerIntN 'Primitive.fromIntegerIntN

--   let numIntN = NumOps { .. }

--   pure IntNOps { .. }

-- data IntegerOps where
--   IntegerOps ::
--     { numInteger :: NumOps
--     } -> IntegerOps

-- getIntegerOps
--   :: HasCallStack
--   => Error (LookupError TH.Name) :> es
--   => Error (LookupError Name) :> es
--   => HasThings :> es
--   => THNameToGHCName :> es
--   => Eff es IntegerOps
-- getIntegerOps = do
--   opAdd <- getOperation 'Primitive.plusInteger
--   opMul <- thNameToId 'Primitive.timesInteger
--   opAbs <- thNameToId 'Primitive.absInteger
--   opSignum <- thNameToId 'Primitive.signumInteger
--   opNegate <- thNameToId 'Primitive.negateInteger
--   opFromInteger <- thNameToId 'Primitive.fromIntegerInteger

--   let numInteger = NumOps { .. }

--   pure IntegerOps { .. }

-- data Operations where
--   Operations ::
--     { opsIntN :: IntNOps
--     -- , opsInteger :: IntegerOps
--     } -> Operations

-- getOperations
--   :: HasCallStack
--   => Error (LookupError TH.Name) :> es
--   => Error (LookupError Name) :> es
--   => Error ReifyMismatch :> es
--   => HasThings :> es
--   => THNameToGHCName :> es
--   => Eff es Operations
-- getOperations = do
--   opsIntN <- getIntNOps
--   -- opsInteger <- getIntegerOps
--   pure Operations { .. }
