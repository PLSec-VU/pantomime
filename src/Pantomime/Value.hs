{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Pantomime.Value
  ( Value (..)
  , mkCast'
  , dumpValue

  , typedValue
  , freshValue
  , invalidValue

  , nArity

  , applyValue
  , applyValues

  , ADT (..)
  , adtType
  , adtFromDataCon
  , adtIsDataCon
  , adtDataConFields

  , Tag
  , dataConToTag
  , tagToDataCon

  , Primitive (..)
  ) where

import GHC.Plugins hiding (empty)
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.TyCo.Rep (Coercion (..), UnivCoProvenance (..), scaledThing)
import GHC.Core.Type (substTy)
import GHC.Core.TyCo.FVs (shallowTyCoVarsOfType)
import GHC.Core.Coercion.Opt
import GHC.Core.Reduction (Reduction (..))
import GHC.Core.FamInstEnv (normaliseType)
import GHC.Builtin.Types.Prim
import GHC.Tc.Utils.TcType (hasTyVarHead, isTyFamFree)
import GHC.Types.TyThing (MonadThings(..))
import GHC.TypeLits (SomeNat (..), someNatVal)

import Grisette.SymPrim
import Grisette.Unified (DecideEvalMode (..), EvalModeTag (..), GetIntN, GetWordN)
import Grisette.Lib.Control.Monad.Except (mrgThrowError)
import Grisette
  ( Solvable (..)
  , SimpleMergeable (..)
  , Mergeable
  , LogicalOp (..)
  , SymOrd (..)
  , SymEq (..)
  , EvalSym (..)
  , GenSymSimple (..)
  )

import Data.List ((!?))
import Data.Foldable (find)
import qualified Data.Typeable as Typeable

import Control.Monad (foldM, unless, forM, guard, when)
import Control.Monad.Except (MonadError (..))

import Clash.Prelude (BitVector, Unsigned, Signed, Bit)

import Pantomime.Util
import Pantomime.WordSize
import Pantomime.Runtime
import Pantomime.MonadEval
import Pantomime.Dict
import Pantomime.Primitive
import qualified Pantomime.Grisette.BitVector as Pantomime
import Pantomime.Monad.GHC

-- TODO: Add comment to what this data type is!
data Value m ws where
  Primitive :: Primitive S ws -> Value m ws
  Poly :: Type -> RuntimeValue S (Ident S) -> Value m ws
  Data :: ADT m ws -> Value m ws
  -- TODO: I don't really like the prime on the name of Cast here. Maybe we
  -- could go for some other name? Perhaps just Newtype, as that's pretty much
  -- what we wrap in there anyway. The alternative would be to just prefix all
  -- options with something like 'V'. Then we can also use VType instead of Ty,
  -- VLam instead of Fun, VCoercion instead of Co, etc. Same for Opaque' btw.
  Cast' :: Coercion -> Value m ws -> Value m ws
  Fun :: Kind  -> (Value m ws -> m (Value m ws)) -> Value m ws
  Ty :: Type -> Value m ws
  Co :: Coercion -> Value m ws
  Opaque'
    :: forall m ws a
     . ( Typeable.Typeable a
       , SimpleMergeable a
       , Mergeable a
       , SymEq a
       , EvalSym a
      -- TODO: Remove the show constraint.
       , Show a
       )
    => Type
    -> RuntimeValue S a
    -> Value m ws

dumpValue
  :: KnownWordSize ws
  => Value m ws
  -> SDoc
dumpValue = \case
  Primitive prim -> dumpPrimitive prim
  Data adt -> do
    let tag = "tag" <+> ppr (adtType adt) <+> ":" <+> text (show $ adtTag adt)
    let fields = ppr $ fmap dumpValue <$> adtFields adt
    hang tag 2 fields
  Poly _ value -> "poly:" <+> text (show value)
  Cast' co val -> dumpValue val <+> "<->" <+> ppr (coercionKindRole co)
  Fun _ _ -> "function: ?"
  Ty ty -> "ty:" <+> ppr ty
  Co co -> "co:" <+> ppr co
  Opaque' ty value -> "opaque" <+> ppr ty <+> ":" <+> text (show value)

dumpPrimitive
  :: DecideEvalMode mode
  => KnownWordSize ws
  => Primitive mode ws
  -> SDoc
dumpPrimitive = \case
  Int value -> "int:" <+> text' value
  Int8 value -> "int8:" <+> text' value
  Int16 value -> "int16:" <+> text' value
  Int32 value -> "int32:" <+> text' value
  Int64 value -> "int64:" <+> text' value
  Word value -> "word:" <+> text' value
  Word8 value -> "word8:" <+> text' value
  Word16 value -> "word16:" <+> text' value
  Word32 value -> "word32:" <+> text' value
  Word64 value -> "word64:" <+> text' value
  Float value -> "float:" <+> text' value
  Double value -> "doube:" <+> text' value
  ByteArray size value -> "bytearray:" <+> text' size <+> text' value
  where
    text' :: Show a => a -> SDoc
    text' = text . show

instance KnownWordSize ws => Outputable (Value m ws) where
  ppr = \case
    Primitive prim -> ppr prim
    Poly ty _ -> ppr ty
    Data adt -> ppr adt
    Cast' co val -> ppr val <+> "<->" <+> ppr (coercionKindRole co)
    Fun argTy _ -> ppr argTy <+> "-> ?"
    Ty ty -> text "@" <+> ppr ty
    Co co -> ppr co
    Opaque' ty _ -> ppr ty

instance (KnownWordSize ws, Functor m) => EvalSym (Value m ws) where
  evalSym fill model = \case
    Primitive prim -> Primitive $ evalSym' prim
    Data adt -> Data $ evalSym' adt
    Poly ty value -> Poly ty $ evalSym' value
    Cast' co value -> Cast' co $ evalSym' value
    Fun argTy fun -> Fun argTy $ \arg -> evalSym' <$> fun arg
    Ty ty -> Ty ty
    Co co -> Co co
    Opaque' ty value -> Opaque' ty $ evalSym' value
    where
      evalSym' :: EvalSym a => a -> a
      evalSym' = evalSym fill model

instance Functor m => Forceable S (Value m ws) where
  force constraints = \case
    Primitive prim -> Primitive $ force' prim
    Poly ty value -> Poly ty $ force' value
    Data adt -> Data $ force' adt
    Cast' co value -> Cast' co $ force' value
    Fun argTy fun -> Fun argTy $ \arg -> force' <$> fun arg
    Opaque' ty value -> Opaque' ty $ force' value
    -- TODO: These aren't really forceable. I guess they needn't be, but it
    -- might create unexpected behaviour.
    Ty _ty -> error "We fail for now"
    Co _co -> error "We fail for now"
    where
      force' :: Forceable S a => a -> a
      force' = force constraints

instance Spineable S (Value m ws) where
  spine = \case
    Primitive prim -> spine prim
    Poly _ value -> spine value
    Data adt -> spine adt
    Cast' _ value -> spine value
    Fun _ _ -> pure ()
    Ty _ -> pure ()
    Co _ -> pure ()
    Opaque' _ value -> spine value

instance (MonadEval m, KnownWordSize ws) => EvalIte m (Value m ws) where
  evalIte cond = curry $ \case
    (Primitive lhs, Primitive rhs) -> Primitive <$> evalIte cond lhs rhs
    (Poly lty lhs, Poly rty rhs) -> do
      unless (lty `eqType` rty) $ throwError IllTyped
      Poly lty <$> evalIte cond lhs rhs
    (Data lhs, Data rhs) -> Data <$> evalIte cond lhs rhs
    (Cast' lco lhs, Cast' rco rhs) -> do
      unless (lco `eqCoercion` rco) $ throwError IllTyped
      result <- evalIte cond lhs rhs
      pure $ Cast' lco result
    (Fun larg lhs, Fun rarg rhs) -> do
      unless (larg `eqType` rarg) $ throwError IllTyped
      pure . Fun larg $ \arg -> do
        lhs' <- lhs arg
        rhs' <- rhs arg
        evalIte cond lhs' rhs'
    (Ty lty, Ty rty) -> do
      unless (lty `eqType` rty) $ throwError IllTyped
      pure $ Ty lty
    (Co lco, Co rco) -> do
      unless (lco `eqCoercion` rco) $ throwError IllTyped
      pure $ Co lco
    (Opaque' @_ @_ @l lty lhs, Opaque' @_ @_ @r rty rhs) -> do
      unless (lty `eqType` rty) $ throwError IllTyped
      Typeable.Refl <- whyFail IllTyped $ Typeable.eqT @l @r
      Opaque' lty <$> evalIte cond lhs rhs
    _ -> throwError IllTyped

-- TODO: We removed strong equivalence now, pehaps this shouldn't be called weak
-- equivalence anymore! Also, I think it would be better if this would return a
-- Constrained SymBool, where Constrained is ExceptT Union Invalid. It seems to
-- me like it would be much better to split the runtime errors from Invalid.
instance (MonadEval m, KnownWordSize ws) => WeakEq m (Value m ws) where
  weakEq = curry $ \case
    (Primitive lhs, Primitive rhs) -> weakEq lhs rhs
    (Data lhs, Data rhs) -> weakEq lhs rhs
    (Cast' lco lhs, Cast' rco rhs) -> do
      unless (lco `eqCoercion` rco) $ throwError IllTyped
      weakEq lhs rhs

    (Fun lty lhs, Fun rty rhs) -> do
      unless (lty `eqType` rty) $ throwError IllTyped
      arg <- freshValue lty
      lhs' <- lhs arg
      rhs' <- rhs arg
      weakEq lhs' rhs'

    (Opaque' @_ @_ @l lty lhs, Opaque' @_ @_ @r rty rhs) -> do
      unless (lty `eqType` rty) $ throwError IllTyped
      Typeable.Refl <- whyFail IllTyped $ Typeable.eqT @l @r
      weakEq lhs rhs

    (Poly lty lhs, Poly rty rhs) -> do
      unless (lty `eqType` rty) $ throwError IllTyped
      weakEq lhs rhs

    (Ty lhs, Ty rhs) -> pure . con $ lhs `eqType` rhs
    (Co lhs, Co rhs) -> pure . con $ lhs `eqCoercion` rhs
    _ -> throwError IllTyped

-- | Create a cast.
--
-- Merges nested casts. This should always be preferred over manually creating
-- a cast.
mkCast'
  :: MonadEval m
  => KnownWordSize ws
  => Coercion
  -> Value m ws
  -> m (Value m ws)
mkCast' c v = case (optimiseCo c, v) of
  -- Before anything else, we just want to get rid of reflexive casts.
  (co, value) | isReflCo co -> pure value

  (co, Cast' co' value) -> do
    -- TODO: Check whether the casts actually can be transitively applied.
    let trans = mkTransCo co' co
    mkCast' trans value

  -- TODO: I guess we shouldn't be pattern matching on the coercion. Instead,
  -- use SelCo to select the right fields from the coercion. Same for FunCo and
  -- TyCoAppCo. This would allow us to drop the optimisation call on every cast.
  -- Do note that for checks on reflexive casts, we would need to use the more
  -- expensive check.
  (co@ForAllCo { fco_kind }, Fun argTy fun) -> do
    let argTy' = coercionRKind fco_kind
    unless (argTy `eqType` coercionLKind fco_kind) $ throwError IllTyped

    pure . Fun argTy' $ \case
      Ty arg -> do
        let arg' = mkCastTy arg $ mkSymCo fco_kind
        result <- fun $ Ty arg'
        let resCo = mkInstCo co $ mkNomReflCo arg'
        mkCast' resCo result
      _ -> throwError IllTyped

  (FunCo { fco_arg, fco_res }, Fun argTy fun) -> do
    let argTy' = coercionRKind fco_arg
    unless (argTy `eqType` coercionLKind fco_arg) $ throwError IllTyped

    pure . Fun argTy' $ \arg -> do
      arg' <- mkCast' (mkSymCo fco_arg) arg
      result <- fun arg'
      mkCast' fco_res result

  (TyConAppCo role tyCon coArgs, Data adt) -> do
    unless (tyCon == adtTyCon adt) $ throwError IllTyped

    -- Gather all DataCons in the ADT.
    dataCons <- whyFail IllTyped $ tyConDataCons_maybe tyCon

    -- Cast the fields of every DataCon.
    fields <- forM dataCons $ \dataCon -> do
      -- Gather the field types with the universal type variables.
      -- TODO: I don't think this works for ADTs with existential types.
      let tyVars = dataConUnivTyVars dataCon
      let tyArgs = scaledThing <$> dataConInstArgTys dataCon (mkTyVarTys tyVars)

      -- Lift the field types to coercions by substituting the type variables
      -- for the coercion arguments.
      let coercions = liftCoSubstWith role tyVars coArgs <$> tyArgs

      -- Cast the fields of the ADT for the current DataCon.
      fields <- whyFail IllTyped $ adtDataConFields adt dataCon
      forM (zip coercions fields) $ uncurry mkCast'

    -- The type arguments are now simply the result type of the coercions.
    let tyArgs = coercionRKind <$> coArgs

    -- Construct the new ADT with the coerced fields.
    pure $ Data ADT
      { adtTyCon = tyCon
      , adtTyArgs = tyArgs
      , adtTag = adtTag adt
      , adtFields = fields
      }

  -- Given some Cast (a ~# b) ~# (c ~# d) on a Coercion (a ~# b), cast the
  -- coercion to (c ~# d).
  (co, Co co') -> do
    let cast = mkCoCast co' co
    pure $ Co cast

  -- TODO: This should be part of an interface to add support for opaque types.
  (TyConAppCo _ tyCon [sizeCo], Opaque' ty value)
    | Just (tyCon', [size]) <- splitTyConApp_maybe ty
    -- TODO: Ensure that we actually deal with the Clash bitvector types! This
    -- transformation may be wrong for other types!
    , tyCon == tyCon'
    , size `eqType` coercionLKind sizeCo -> do
    let size' = coercionRKind sizeCo
    let ty' = mkTyConApp tyCon [size']
    pure $ Opaque' ty' value

  -- TODO: Check whether the coercion actually fits the value.
  (co, value) -> pure $ Cast' co value

optimiseCo :: Coercion -> Coercion
optimiseCo = optCoercion (OptCoercionOpts True) emptySubst

-- | Unintepreted identifier.
--
-- This may represent any abstract value, such as a function pointer.
type Ident mode = GetWordN mode 64

-- | A Constraint alias that captures interpretations on an identifier.
type Interpretable t = Solvable (Ident C --> ConType t) (Ident S -~> t)

-- | Constraints for creating the symbolic values we require.
--
-- These constraints are picked such that we can avoid overlapping instances
-- whilst allowing all values we require to be constructed.
type Symbolisable t ws =
  ( Mergeable t
  , LinkedRep (ConType t) t
  , Solvable (ConType t) t
  , Interpretable t
  , Interpretable (SymIntN (WordBits ws) -~> t)
  , Interpretable (SymIntN8 -~> t)
  , Interpretable (SymIntN16 -~> t)
  , Interpretable (SymIntN32 -~> t)
  , Interpretable (SymIntN64 -~> t)
  , Interpretable (SymWordN (WordBits ws) -~> t)
  , Interpretable (SymWordN8 -~> t)
  , Interpretable (SymWordN16 -~> t)
  , Interpretable (SymWordN32 -~> t)
  , Interpretable (SymWordN64 -~> t)
  , Interpretable (SymFP32 -~> t)
  , Interpretable (SymFP64 -~> t)
  )

-- TODO: Maybe move this somewhere else? This is more of a utility function.
eqTyConRole :: TyCon -> Maybe Role
eqTyConRole tyCon = if
  | tyCon == eqPrimTyCon -> Just Nominal
  | tyCon == eqReprPrimTyCon -> Just Representational
  | tyCon == eqPhantPrimTyCon -> Just Phantom
  | otherwise -> Nothing

-- Goal:
--
-- Support OPAQUE expressions from Clash. These should get a handwritten
-- bitvector interpretation.
--
-- Steps:
--
-- Allow us to create symbolic instances for opaque types. I.e. BitVector should
-- get a SymWordN symbolic instance.
-- - To actuate this, we need to be able to access the TyCons of the things we
--   wish to interpret. This should be done through lookupTyCon/lookupTyThing.
--   It would be best to look this up once, but we could get away with doing the
--   lookup inside typedValue, since we are in the CoreM monad for debugging
--   purposes.
-- - Apart from this, we really should be able to split the typedValue function
--   into separate checks. This allows us to easily extend it!
--
-- Allow us to create symbolic instances for opaque functions. We already have
-- something like this going. I guess in the ideal world, we allow user defined
-- interpretations through some interface. Then we define a Clash interpretation
-- outside of the base symbolic executor. This would be much cleaner. For now
-- though, we don't have enough time... :(
--
-- - Short term solution would be to add variable size bitvector as a primitive.
--   Then we can use the existing method to add interpretation to the clash
--   opaque functions.
--
-- - After the deadline, we should consider adding in an Opaque constructor to
--   Value. It would have an existential value in it, with some constraints
--   (i.e. it should implement some of the interfaces we use for merging,
--   if then else, etc.). We could btw reuse this to do polymorphic instances,
--   since they are, in a way, also opaque. Then we could interface the Opaque
--   constructor to allow for users to interpret values and create symbolic
--   values.

-- TODO: I guess this should just return a maybe, as there is only one reason
-- why this would possibly fail. We only return IllTyped when nested values
-- occur. I think we can actually capture this idea in a typeclass (perhaps
-- called symbolise), which takes a Type and returns itself (if possible).
-- TODO: We should remove all uses of this in favor of the new interface!
typedValue
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  -- TODO: I think with the new setup this is way to general of a thing to want?
  -- I think at this point, we just want to eliminitate this argument entirely
  -- and just assume some stuff on a value afterwards if required no?
  => (forall t. Symbolisable t ws => RuntimeValue S t)
  -> Type
  -> m (Value m ws)
typedValue value ty = evalFresh (ty, spec)
  where
    spec = if
      | value @SymIntN64 == throwError Invalid -> Left Invalid
      | otherwise -> Right ()

instance
  ( MonadEval m
  , RuntimeGenSymSimple spec
  , KnownWordSize ws
  ) => EvalGenSym m (Type, spec) (Value m ws) where
  evalFresh spec@(ty, _) = asum'
    [ freshBitVector spec
    , freshUnsigned spec
    , freshSigned spec
    , freshBit spec
    , Primitive <$> evalFresh spec
    , freshTyFamInst spec
    , freshNewtype spec
    , freshLambda spec
    , Data <$> evalFresh spec
    , freshForall spec
    , freshPoly spec
    , freshCoercion ty
    , freshType ty
    ]
    where
      asum' :: [m a] -> m a
      asum' [] = dbg ty >> throwError UnsupportedExpr
      asum' (x:xs) = x `catchError` \case
        UnsupportedExpr -> asum' xs
        err -> throwError err

-- TODO: This should be defined outside of the base definitions. We should have
-- an import interface to allow interpretations like this one! Also, I think we
-- should be able to make interpretations less techinical... At the end of the
-- day it's just a check: does the type match this pattern, then use this opaque
-- interpretation instead.
freshBitVector
  :: forall m ws spec
   . MonadEval m
  => RuntimeGenSymSimple spec
  => (Type, spec)
  -> m (Value m ws)
freshBitVector (ty, spec) = do
  -- Get the TyCon and type literal of this type, if possible.
  (tyCon, SomeNat @n _) <- case tcSplitTyConApp_maybe ty of
    Just (tyCon, [size])
      | Just size' <- normNumLitTy size >>= someNatVal
      -- TODO: Additionally check whether the integer conversion is not lossy.
      -> pure (tyCon, size')
    _ -> throwError UnsupportedExpr

  -- Ensure the TyCon is actually a BitVector.
  -- TODO: We should really not be looking up the name here! This should just be
  -- some pre-pass thing imo.
  bvTyCon <- do
    name <- liftCore $ thNameToGhcName ''BitVector
    name' <- whyFail UnsupportedExpr name
    liftCore $ lookupTyCon name'
  unless (tyCon == bvTyCon) $ throwError UnsupportedExpr

  bv :: RuntimeValue S (Pantomime.WordN S n) <- simpleFresh spec
  pure $ Opaque' ty bv

-- TODO: This is a lot of code duplication. Can't we squash this one with
-- typedBitVector?
freshUnsigned
  :: forall m ws spec
   . MonadEval m
  => RuntimeGenSymSimple spec
  => (Type, spec)
  -> m (Value m ws)
freshUnsigned (ty, spec) = do
  -- Get the TyCon and type literal of this type, if possible.
  (tyCon, SomeNat @n _) <- case tcSplitTyConApp_maybe ty of
    Just (tyCon, [size])
      | Just size' <- normNumLitTy size >>= someNatVal
      -- TODO: Additionally check whether the integer conversion is not lossy.
      -> pure (tyCon, size')
    _ -> throwError UnsupportedExpr

  -- Ensure the TyCon is actually an Unsigned.
  -- TODO: We should really not be looking up the name here! This should just be
  -- some pre-pass thing imo.
  bvTyCon <- do
    name <- liftCore $ thNameToGhcName ''Unsigned
    name' <- whyFail UnsupportedExpr name
    liftCore $ lookupTyCon name'
  unless (tyCon == bvTyCon) $ throwError UnsupportedExpr

  bv :: RuntimeValue S (Pantomime.WordN S n) <- simpleFresh spec
  pure $ Opaque' ty bv

freshSigned
  :: forall m ws spec
   . MonadEval m
  => RuntimeGenSymSimple spec
  => (Type, spec)
  -> m (Value m ws)
freshSigned (ty, spec) = do
  -- Get the TyCon and type literal of this type, if possible.
  (tyCon, SomeNat @n _) <- case tcSplitTyConApp_maybe ty of
    Just (tyCon, [size])
      | Just size' <- someTyNat size
      -- TODO: Additionally check whether the integer conversion is not lossy.
      -> pure (tyCon, size')
    _ -> throwError UnsupportedExpr

  -- Ensure the TyCon is actually a Signed.
  -- TODO: We should really not be looking up the name here! This should just be
  -- some pre-pass thing imo.
  bvTyCon <- do
    name <- liftCore $ thNameToGhcName ''Signed
    name' <- whyFail UnsupportedExpr name
    liftCore $ lookupTyCon name'
  unless (tyCon == bvTyCon) $ throwError UnsupportedExpr

  bv :: RuntimeValue S (Pantomime.IntN S n) <- simpleFresh spec
  pure $ Opaque' ty bv

freshBit
  :: forall m ws spec
   . MonadEval m
  => RuntimeGenSymSimple spec
  => (Type, spec)
  -> m (Value m ws)
freshBit (ty, spec) = do
  -- Get the TyCon and type literal of this type, if possible.
  tyCon <- case tcSplitTyConApp_maybe ty of
    Just (tyCon, []) -> pure tyCon
    _ -> throwError UnsupportedExpr

  -- Ensure the TyCon is actually a Bit.
  -- TODO: We should really not be looking up the name here! This should just be
  -- some pre-pass thing imo.
  bitTyCon <- do
    name <- liftCore $ thNameToGhcName ''Bit
    name' <- whyFail UnsupportedExpr name
    liftCore $ lookupTyCon name'
  unless (tyCon == bitTyCon) $ throwError UnsupportedExpr

  bv :: RuntimeValue S (Pantomime.WordN S 1) <- simpleFresh spec
  pure $ Opaque' ty bv

freshTyFamInst
  :: forall m ws spec
   . MonadEval m
  => KnownWordSize ws
  => RuntimeGenSymSimple spec
  => (Type, spec)
  -> m (Value m ws)
freshTyFamInst (ty, spec) = do
  -- Ensure there are type families here.
  when (isTyFamFree ty) $ throwError UnsupportedExpr

  -- Gather the type family instances.
  famInst <- getFamInstEnvs'

  -- Get the inner type after reducing the type family instances.
  -- TODO: Shouldn't we check whether Nominal normalisation returns the same
  -- coercion? What about the Phantom role?
  let reduction = normaliseType famInst Representational ty
  let co = SymCo $ reductionCoercion reduction
  let ty' = reductionReducedType reduction

  -- Ensure there is an actual reduction.
  when (isReflexiveCo co) $ throwError UnsupportedExpr

  -- Create the cast.
  inner <- evalFresh (ty', spec)
  mkCast' co inner

freshNewtype
  :: forall m ws spec
   . MonadEval m
  => KnownWordSize ws
  => RuntimeGenSymSimple spec
  => (Type, spec)
  -> m (Value m ws)
freshNewtype (ty, spec) = do
  (tyCon, tys) <- whyFail UnsupportedExpr $ tcSplitTyConApp_maybe ty
  (ty', co) <- whyFail UnsupportedExpr $ instNewTyCon_maybe tyCon tys
  value' <- evalFresh (ty', spec)
  let co' = mkSymCo co
  mkCast' co' value'

-- FIXME: This one was already broken with the previous setup. For now, we just
-- simplified it, but the correctness is the same (only good for error
-- generation). For now, this is all we need though, as we do not symbolic
-- function arguments at the top level.
freshLambda
  :: forall m ws spec
   . MonadEval m
  => KnownWordSize ws
  => RuntimeGenSymSimple spec
  => (Type, spec)
  -> m (Value m ws)
freshLambda (ty, spec) = do
  (_, _, argTy, resTy) <- whyFail UnsupportedExpr $ splitFunTy_maybe ty
  pure . Fun argTy $ \_ -> do
    evalFresh (resTy, spec)

freshForall
  :: forall m ws spec
   . MonadEval m
  => KnownWordSize ws
  => RuntimeGenSymSimple spec
  => (Type, spec)
  -> m (Value m ws)
freshForall (ty, spec) = do
  (tyCoVar, resTy) <- whyFail UnsupportedExpr $ splitForAllTyCoVar_maybe ty
  let vars = shallowTyCoVarsOfType ty
  let subst = mkEmptySubst $ InScope vars

  let argKind = tyVarKind tyCoVar
  -- TODO: This should not be a function accepting both a coercion variable or
  -- type variable. Instead, two individual functions should be made for each
  -- case.
  pure . Fun argKind $ \case
    Ty arg -> do
      let subst' = extendTvSubst subst tyCoVar arg
      let resTy' = substTy subst' resTy
      evalFresh (resTy', spec)

    Co arg -> do
      let subst' = extendCvSubst subst tyCoVar arg
      let resTy' = substTy subst' resTy
      evalFresh (resTy', spec)

    _ -> throwError IllTyped

freshCoercion
  :: forall m ws
   . MonadEval m
  => Type
  -> m (Value m ws)
freshCoercion ty = do
  -- Ensure we have a coercion type.
  (tyCon, a, b) <- case tcSplitTyConApp_maybe ty of
    Just (tyCon, [_, _, a, b]) -> pure (tyCon, a, b)
    _ -> throwError UnsupportedExpr
  role <- whyFail UnsupportedExpr $ eqTyConRole tyCon

  -- TODO: In reality, shouldn't we only be able to construct valid coercions
  -- here. I guess otherwise, we would need to return Invalid. The problem is,
  -- we currently don't allow Invalid in a coercion.
  let provenance = PluginProv "Unsound placeholder"
  let coercion = mkUnivCo provenance role a b
  pure $ Co coercion

freshType
  :: forall m ws
   . MonadEval m
  => Type
  -> m (Value m ws)
freshType ty = if
  | isTypeLikeKind ty -> pure $ Ty alphaTy
  | otherwise -> throwError UnsupportedExpr

freshPoly
  :: forall m ws spec
   . MonadEval m
  => RuntimeGenSymSimple spec
  => (Type, spec)
  -> m (Value m ws)
freshPoly (ty, spec) = if
  | hasTyVarHead ty -> Poly ty <$> simpleFresh spec
  | otherwise -> throwError UnsupportedExpr

-- | Create an unconstrained, typed value.
freshValue
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => Type
  -> m (Value m ws)
freshValue ty = evalFresh (ty, Right @() ())

-- | A value that should not be reachable.
--
-- It will be typed according to the given core type.
invalidValue 
  :: forall m ws
   . MonadEval m
  => KnownWordSize ws
  => Type
  -> m (Value m ws)
invalidValue ty = evalFresh (ty, Left @_ @() Invalid)

-- | Create a function with the arity of whatever we are folding over.
--
-- Use the accumulation function to pass data to the root value of the function.
-- We do it in this way as we cannot just pass values into a Haskell lambda.
nArity
  :: forall m t ws a b
   . Monad m
  => Foldable t
  => (b -> m (Value m ws))
  -- ^ Root value and what we accumulate.
  -> t (a, Kind)
  -- ^ What we fold over. Decides the arity of the function.
  -> (b -> a -> Value m ws -> m b)
  -- ^ Accumulation function
  -> m (b -> m (Value m ws))
nArity acc xs f = foldrM' acc xs $ \(x, argTy) acc' -> do
  pure $ \y -> pure . Fun argTy $ \arg -> do
    res <- f y x arg
    acc' res

-- | Apply a function to a value.
--
-- This will fail if the first value is not a function, or if the inner function
-- throws upon receiving the argument.
applyValue
  :: MonadEval m
  => Value m ws
  -> Value m ws
  -> m (Value m ws)
applyValue = curry $ \case
  (Fun _ fun, arg) -> fun arg
  _ -> throwError IllTyped

-- | Apply the given arguments.
--
-- A foldM over a call of 'applyValue'.
applyValues
  :: MonadEval m
  => Value m ws
  -> [Value m ws]
  -> m (Value m ws)
applyValues = foldM applyValue

data ADT m ws where
  ADT ::
    { adtTyCon :: TyCon
    , adtTyArgs :: [Type]
    , adtTag :: Tag S ws
    , adtFields :: [[Value m ws]]
    } -> ADT m ws

instance KnownWordSize ws => Outputable (ADT m ws) where
  ppr = ppr . adtType

instance (Functor m, KnownWordSize ws) => EvalSym (ADT m ws) where
  evalSym fill model adt = do
    let evalSym' :: EvalSym a => a -> a
        evalSym' = evalSym fill model
    adt
      { adtTag = evalSym' $ adtTag adt
      , adtFields = fmap evalSym' <$> adtFields adt
      }

instance (MonadEval m, KnownWordSize ws) => EvalIte m (ADT m ws) where
  evalIte cond lhs rhs = do
    unless (adtType lhs `eqType` adtType rhs) $ throwError IllTyped

    -- If-then-else both the tag and the fields.
    tag <- evalIte cond (adtTag lhs) (adtTag rhs)
    fields' <- zipFieldsWith (evalIte cond) lhs rhs

    pure lhs
      { adtTag = tag
      , adtFields = fields'
      }

instance Forceable S (ADT m ws) where
  force constraints adt = adt
    { adtTag = force constraints $ adtTag adt
    }

instance Spineable S (ADT m ws) where
  spine = spine . adtTag

instance (MonadEval m, KnownWordSize ws) => WeakEq m (ADT m ws) where
  weakEq lhs rhs = do
    unless (adtType lhs `eqType` adtType rhs) $ throwError IllTyped

    -- Ensure the tags are equivalent.
    -- FIXME: This doesn't deal with comparison of error values. The semantic
    -- for errors should be that the fields can be any value if both tags are
    -- the same error.
    -- TODO: This probably also creates duplicate constraints. There should be
    -- a better way to encode this.
    let tagCmp = liftA2 (.==) (adtTag lhs) (adtTag rhs)
    let invalidTag = tagCmp .== throwError Invalid
    let tagEq = tagCmp .== pure true

    -- First join all fields in pairs. I.e. for every DataCon, we pair all
    -- fields.
    joint <- zipFieldsWith weakEq lhs rhs

    -- Gather the field equalities for each DataCon.
    fieldEq <- forM (zip [0..] joint) $ \(tag, eqs) -> do
      -- Both tags match the DataCon. We check for both, as we might collapse
      -- some branches if one of them does not match.
      isTag <- do
        l <- weakEq (adtTag lhs) $ pure (con tag)
        r <- weakEq (adtTag rhs) $ pure (con tag)
        pure $ l .&& r

      -- All fields are equal.
      let fieldEq = foldl' (.&&) true eqs

      -- The fields should be equal given that the tag matches.
      pure $ symImplies isTag fieldEq

    -- The tags should be equivalent and the fields of the matching DataCon
    -- should be equivalent.
    pure $ invalidTag .|| foldl' (.&&) tagEq fieldEq

instance
  ( MonadEval m
  , KnownWordSize ws
  , RuntimeGenSymSimple spec
  ) => EvalGenSym m (Type, spec) (ADT m ws) where
  evalFresh (ty, spec) = do
    -- Ensure this is a ADT we can construct
    (tyCon, tyArgs) <- whyFail UnsupportedExpr $ tcSplitTyConApp_maybe ty
    let isADT = or
          [ isDataTyCon tyCon
          , isUnboxedTupleTyCon tyCon
          , isUnboxedSumTyCon tyCon
          ]
    unless isADT $ throwError UnsupportedExpr
    dataCons <- whyFail UnsupportedExpr $ tyConDataCons_maybe tyCon
    -- TODO: This will loop infinitely for recursive types. We need to resolve
    -- that somehow.

    -- Create a fresh tag.
    tag <- freshTag (tyCon, spec)

    -- Create fresh values for all fields.
    fields <- forM dataCons $ \dataCon -> do
      freshBndrs dataCon tyArgs spec

    pure $ ADT
      { adtTyCon = tyCon
      , adtTyArgs = tyArgs
      , adtTag = tag
      , adtFields = fields
      }

-- | Create fresh binders for the given DataCon.
--
-- Note the type arguments will instantiate the universal quantifiers of the
-- DataCon. They do not correspond to the types of the binders.
freshBndrs
  :: MonadEval m
  => KnownWordSize ws
  => RuntimeGenSymSimple spec
  => DataCon
  -> [Type]
  -> spec
  -> m [Value m ws]
freshBndrs dataCon tyArgs spec = do
  let fieldTys = scaledThing <$> dataConInstArgTys dataCon tyArgs
  forM fieldTys $ evalFresh . (,spec)

-- | Get the Type of an ADT.
adtType :: ADT m ws -> Type
adtType adt = mkTyConApp (adtTyCon adt) (adtTyArgs adt)

-- | Create an ADT that matches the given DataCon.
--
-- The Type arguments are the universal quantifier instances of the TyCon.
-- The Value arguments are the fields that match the given DataCon.
adtFromDataCon
  :: KnownWordSize ws
  => MonadEval m
  => DataCon
  -> [Type]
  -> [Value m ws]
  -> m (ADT m ws)
adtFromDataCon dataCon tyArgs fields = do
  -- Get the TyCon for this ADT.
  let tyCon = dataConTyCon dataCon

  -- Gather all DataCons for populating the ADT.
  dataCons <- whyFail IllTyped $ tyConDataCons_maybe tyCon

  -- Populate the remaining fields with fresh values.
  fields' <- forM dataCons $ \dataCon' -> if
    | dataCon == dataCon' -> pure fields
    | otherwise -> freshBndrs dataCon' tyArgs $ Left @_ @() Invalid

  pure ADT
    { adtTyCon = tyCon
    , adtTyArgs = tyArgs
    , adtTag = pure $ dataConToTag dataCon
    , adtFields = fields'
    }

-- | Zip the fields of two ADTs.
--
-- Note, this does not check whether the ADTs are of the same type.
zipFieldsWith
  :: Monad m
  => (Value m ws -> Value m ws -> m a)
  -> ADT m ws
  -> ADT m ws
  -> m [[a]]
zipFieldsWith f lhs rhs = do
  let outer = zip (adtFields lhs) (adtFields rhs)
  let inner = sequence . uncurry (zipWith f) <$> outer
  sequence inner

-- | Whether the tag of this ADT is equivalent to the DataCon.
adtIsDataCon
  :: KnownWordSize ws
  => ADT m ws
  -> DataCon
  -> RuntimeValue S SymBool
adtIsDataCon adt dataCon = do
  let tag = dataConToTag dataCon
  (.== con tag) <$> adtTag adt

-- | Get the fields of the ADT that match the DataCon.
--
-- Throws an error if the DataCon does not match the ADT.
adtDataConFields
  :: forall m ws
   . KnownWordSize ws
  => ADT m ws
  -> DataCon
  -> Maybe [Value m ws]
adtDataConFields adt dataCon = do
  guard $ adtTyCon adt == dataConTyCon dataCon
  let tag = dataConToTag @C @ws dataCon
  adtFields adt !? fromIntegral tag

type Tag mode ws = RuntimeValue mode (GetIntN mode (WordBits ws))

-- | Convert a DataCon into an SMT solvable Tag.
dataConToTag
  :: Num (GetIntN mode (WordBits ws))
  => DataCon
  -- TODO: I really want to return a Tag here, but it is a bit ugly... That is,
  -- the tag doesn't need to be in the monad in this instance.
  -> GetIntN mode (WordBits ws)
dataConToTag = fromIntegral . dataConTagZ

-- | Get the DataCon from a Tag and the Type that should match the .
tagToDataCon
  :: forall ws
   . KnownWordSize ws
  => IntN (WordBits ws)
  -> TyCon
  -> Maybe DataCon
tagToDataCon tag tyCon = do
  dataCons <- tyConDataCons_maybe tyCon
  let cmp = (tag ==) . fromIntegral . dataConTagZ
  find cmp dataCons

-- | Create a fresh 'Tag' for the given 'TyCon'.
freshTag
  :: forall m ws spec
   . KnownWordSize ws
  => MonadEval m
  => GenSymSimple spec (RuntimeValue S (SymIntN (WordBits ws)))
  => (TyCon, spec)
  -> m (Tag S ws)
freshTag (tyCon, spec) = do
  tag :: Tag S ws <- simpleFresh spec
  pure $ do
    -- Ensure the tag is within range
    tag' <- tag
    let variants = length $ tyConDataCons tyCon
    let bound = 0 .<= tag' .&& tag' .< fromIntegral variants
    mrgIte bound tag $ mrgThrowError Invalid
