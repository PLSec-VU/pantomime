-- TODO: I'm not sure about this module name. It looks as though it's about
-- GHC primitives. In reality, we just lookup all the GHC information before we
-- can perform the interpretations.
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Primitive.GHC
  ( Types (..)
  , getTypes

  , ReifyMismatch (..)
  , reifiedIntN

  , reifiedBase

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

import Pantomime.Expr (Eval, Expr, failWithE, throwE)
import Pantomime.Grisette.SomeBV (SomeBV(..))
import Pantomime.Grisette.BitVector (IntN)
import Pantomime.Primitive.Operations qualified as Primitive
import Pantomime.Primitive.Reify

import Data.Typeable (type (:~:) (..), eqT)

import Control.Monad (unless, (>=>))

import GHC.TypeLits (KnownNat)
import GHC.Num (integerToInt#, integerToWord#)

import Effectful
import Effectful.Error.Static
import Effectful.GHC.TH
import Effectful.GHC.TyThing
import Effectful.Exception (throwIO)

import Grisette.Unified (EvalModeTag (..))
import Grisette (SignConversion(..))

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

data Interpretation where
  Interpretation :: Reify a => TH.Name -> Eval (InterpRep a) -> Interpretation

lookupReify
  :: forall a es
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error ReifyMismatch :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Reify a
  => TH.Name
  -> Eval (InterpRep a)
  -> Eff es (Var, Eval Expr)
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
  ty <- reifiedType @a

  -- Ensure that the interpretation has a proper reified type.
  unless (eqType ty $ varType var) do
    throwError_ $ ReifyMismatch var ty

  -- Get the expression reified from the intepretation.
  let expr = reify @a ty interp
  pure (var, expr)

lookupReifyMany
  :: forall f es
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error ReifyMismatch :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Traversable f
  => f Interpretation
  -> Eff es (f (Var, Eval Expr))
lookupReifyMany = traverse \(Interpretation @r name interp) -> do
  lookupReify @r name interp

reifiedIntN
  :: forall es
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Eff es [(Var, Eval Expr)]
reifiedIntN = staticReifyError $ lookupReifyMany
  [ binary 'Primitive.plusIntN (+)
  , binary 'Primitive.timesIntN (*)
  , unary 'Primitive.absIntN abs
  , unary 'Primitive.signumIntN signum
  , unary 'Primitive.negateIntN negate
  -- , binary 'Primitive.fromIntegerIntN
  ]
  where
    binary
      :: TH.Name
      -> (forall n. KnownNat n => IntN S n -> IntN S n -> IntN S n)
      -> Interpretation
    binary name op = Interpretation @BinaryIntN name $ liftF4 \_n c x y -> do
      _ <- c
      -- TODO: Should we check that the KnownNat is indeed equal to the size of
      -- the bitvector?
      SomeBV @n x' <- x
      SomeBV @m y' <- y
      Refl <- failWithE () $ eqT @n @m
      pure . SomeBV $ op x' y'

    unary
      :: TH.Name
      -> (forall n. KnownNat n => IntN S n -> IntN S n)
      -> Interpretation
    unary name op = Interpretation @UnaryIntN name $ liftF3 \_n c x -> do
      _ <- c
      SomeBV x' <- x
      pure . SomeBV $ op x'

-- TODO: The only reason we need to reify these is because of the NOINLINE
-- pragma. Perhaps it makes more sense to use the user-interpretation stuff once
-- we have it implemented. The only thing we would need to do is to copy-paste
-- the code that has a NOINLINE pragma and then provide it as an interp for the
-- NOINLINE code.
reifiedBase
  :: forall es
   . HasCallStack
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => Eff es [(Var, Eval Expr)]
reifiedBase = staticReifyError $ lookupReifyMany
  -- FIXME: Get proper architecture size.
  [ Interpretation @(RInteger ~> RHIntPW 64) 'integerToInt# $ pure \x -> do
    x' <- x
    case x' of
      Left (SomeBV @n value)
        -- FIXME: Use proper architecture size on this comparison.
        | Just Refl <- eqT @n @64 -> pure value
      Left _ -> throwE ()
      Right () -> undefined

  , Interpretation @(RInteger ~> RHWordPW 64) 'integerToWord# $ pure \x -> do
    x' <- x
    case x' of
      Left (SomeBV @n value)
        -- FIXME: Use proper architecture size on this comparison.
        | Just Refl <- eqT @n @64 -> pure $ toUnsigned value
      Left _ -> throwE ()
      Right () -> undefined
  ]

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
