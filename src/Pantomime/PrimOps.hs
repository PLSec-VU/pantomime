module Pantomime.PrimOps
  -- | System Fc operations.
  ( ite
  , tagToEnum
  , dataToTag

  -- | Boolean operations.
  , true
  , false
  , not
  , implies
  , and
  , or
  , iff
  , xor

  -- | Integer operations.
  , ineg
  , iabs
  , iadd
  , imul
  , idiv
  , imod
  , ieq
  , ineq
  , ile
  , ilt

  -- | Bitvector primitive operations.
  , bvnot
  , bvneg
  , bvand
  , bvor
  , bvxor
  , bvadd
  , bvmul
  , bvudiv
  , bvsdiv
  , bvurem
  , bvsrem
  , bvshl
  , bvlshr
  , bvashr
  , bveq
  , bvneq
  , bvule
  , bvsle
  , bvult
  , bvslt
  , bvconcat
  , bvselect

  -- | Array primitive operations.
  , aconst
  , aselect
  , astore
  ) where

import Data.Bits (Bits((.&.), (.|.), complement))
import Data.Bits qualified as Bits (xor)
import Data.Typeable (type (:~:) (..), eqT, Proxy (..))

import Effectful
import Effectful.Context
import Effectful.Error.Static
import Effectful.GHC.External (HasFamInstEnvs)

import GHC.Plugins (emptySubst, dataConTagZ)
import GHC.TypeLits (type (<=), SomeNat (..))

import Grisette
  ( SymIntN
  , SymBool
  , SymInteger
  , SizedBV (..)
  , SymShift (..)
  , SignConversion (..)
  , SymEq (..)
  , SymOrd (..)
  , LogicalOp (symNot, symImplies, (.&&), (.||))
  , SimpleMergeable (..)
  )
import Grisette qualified (LogicalOp (true, false))
import Grisette.Internal.SymPrim.SymArray qualified as Array

import Pantomime.Embed
import Pantomime.Expr (EvalExpr, failWithE, Expr (..), throwE, mkLit, mkEnumCon, Constructor (..), collectArgs)
import Pantomime.Literal
  ( BuiltInTyCon
  , SomeLiteralType (..)
  , Literal (..)
  , LiteralTypeable (..)
  , HasDict (..)
  , eqLiteralType
  )
import Pantomime.Util (SomeBitVec(..), KnownPos, SymBitVec)
import Pantomime.Dict
import Prelude
  ( Applicative (..)
  , Monad (..)
  , Num (..)
  , Integral (..)
  , Maybe (..)
  , ($)
  , (<$>)
  , fst
  , fromIntegral
  )

-- TODO: It might make sense to expose equality (and especially 'distinct') as
-- an operation over a list of elements. Probably we first want to support
-- sequences if we plan on doing this? In any case, this might be useful to
-- expose at some point. For now, we'll leave it as is.

-- TODO: We should implement some conversion operations. Specifically conversion
-- between bitvec and integer is important. Not sure if there are others? Maybe
-- real numbers once we support them?

type PrimOpExpr es
   = HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => EvalExpr es

-- :: forall r (a :: TYPE r). Bool -> r -> r -> r
type ITEOp
  =   Forall 0 RuntimeRepTy
  :.  Forall 1 (TyVar 0 RuntimeRepTy)
  :.  BoolTy
  :-> TyVar 1 (TyVar 0 RuntimeRepTy)
  :-> TyVar 1 (TyVar 0 RuntimeRepTy)
  :-> TyVar 1 (TyVar 0 RuntimeRepTy)

ite :: PrimOpExpr es
ite = embed @ITEOp emptySubst $ liftF5 \_ _ scrut tr fl -> do
  scrut' <- scrut
  mrgIte scrut' tr fl

-- TODO: I guess the size of the bitvector is dependent on the platform size.
-- Not sure how to handle this, but for now I'll settle with just using 64-bit.
-- | forall a. BitVec 64 -> a
type TagToEnumOp
  =   Forall 0 TypeKind
  :.  BitVecTy (Natural 64)
  :-> TyVar 0 TypeKind

tagToEnum :: PrimOpExpr es
tagToEnum = embed @TagToEnumOp emptySubst $ liftF2 \ty bvE -> do
  SomeBitVec @n bv <- bvE
  Refl <- failWithE () $ eqT @n @64
  -- TODO: I'm not sure how this interacts with the whole type normalisation.
  -- I don't think this is correct. Maybe we should reduce the type first? I
  -- guess we could also opt to do this within the embedding. This one is likely
  -- just faulty.
  mkEnumCon bv ty

-- forall (l :: Levity) (a :: TYPE (Boxed l)). l -> Int#
type DataToTagOp
  =   Forall 0 LevityTy
  :.  Forall 1 (BoxedRep (TyVar 0 LevityTy))
  :.  TyVar 1 (BoxedRep (TyVar 0 LevityTy))
  :-> BitVecTy (Natural 64)

dataToTag :: PrimOpExpr es
dataToTag = embed @DataToTagOp emptySubst $ liftF3 \_ _ valueE -> do
  value <- valueE
  -- TODO: Maybe we should make the conversion a function inside of
  -- Pantomime.Expr? It feels a bit odd here.
  case fst $ collectArgs value of
    Con (DataCon dc) -> pure $ SomeBitVec @64 (fromIntegral $ dataConTagZ dc)
    Con (EnumCon @n tag _) | Just Refl <- eqT @n @64 -> pure $ SomeBitVec tag
    _ -> throwE ()

true :: PrimOpExpr es
true = embed @BoolTy emptySubst $ pure Grisette.true

false :: PrimOpExpr es
false = embed @BoolTy emptySubst $ pure Grisette.false

not :: PrimOpExpr es
not = embed @(BoolTy :-> BoolTy) emptySubst $ liftF1 \value -> do
  symNot <$> value

boolbinary
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => (SymBool -> SymBool -> SymBool)
  -> EvalExpr es
boolbinary f = embed @(BoolTy :-> BoolTy :-> BoolTy) emptySubst $ liftF2 \lhs rhs -> do
  lhs' <- lhs
  rhs' <- rhs
  pure $ f lhs' rhs'

implies :: PrimOpExpr es
implies = boolbinary symImplies

and :: PrimOpExpr es
and = boolbinary (.&&)

or :: PrimOpExpr es
or = boolbinary (.||)

iff :: PrimOpExpr es
iff = boolbinary (.==)

xor :: PrimOpExpr es
xor = boolbinary (./=)

ineg :: PrimOpExpr es
ineg = embed @(IntegerTy :-> IntegerTy) emptySubst $ liftF1 \value -> do
  negate <$> value

iabs :: PrimOpExpr es
iabs = embed @(IntegerTy :-> IntegerTy) emptySubst $ liftF1 \value -> do
  abs <$> value

ibinary
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => (SymInteger -> SymInteger -> SymInteger)
  -> EvalExpr es
ibinary f = embed @(IntegerTy :-> IntegerTy :-> IntegerTy) emptySubst $ liftF2 \lhs rhs -> do
  lhs' <- lhs
  rhs' <- rhs
  pure $ f lhs' rhs'

iadd :: PrimOpExpr es
iadd = ibinary (+)

imul :: PrimOpExpr es
imul = ibinary (*)

idiv :: PrimOpExpr es
idiv = ibinary div

imod :: PrimOpExpr es
imod = ibinary mod

icompare
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => (SymInteger -> SymInteger -> SymBool)
  -> EvalExpr es
icompare f = embed @(IntegerTy :-> IntegerTy :-> BoolTy) emptySubst $ liftF2 \lhs rhs -> do
  lhs' <- lhs
  rhs' <- rhs
  pure $ f lhs' rhs'

ieq :: PrimOpExpr es
ieq = icompare (.==)

ineq :: PrimOpExpr es
ineq = icompare (./=)

ile :: PrimOpExpr es
ile = icompare (.<=)

ilt :: PrimOpExpr es
ilt = icompare (.<)

type UnBitVecOp
  =   Forall 0 NaturalTy
  :.  BitVecTy (TyVar 0 NaturalTy)
  :-> BitVecTy (TyVar 0 NaturalTy)

bvunary
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => (forall n. KnownPos n => SymBitVec n -> SymBitVec n)
  -> EvalExpr es
bvunary f = embed @UnBitVecOp emptySubst $ liftF2 \_n bv -> do
  SomeBitVec bv' <- bv
  pure $ SomeBitVec (f bv')

-- | Bitvector bitwise complement.
bvnot :: PrimOpExpr es
bvnot = bvunary complement

-- | Bitvector negation.
bvneg :: PrimOpExpr es
bvneg = bvunary negate

type BinBitVecOp
  =   Forall 0 NaturalTy
  :.  BitVecTy (TyVar 0 NaturalTy)
  :-> BitVecTy (TyVar 0 NaturalTy)
  :-> BitVecTy (TyVar 0 NaturalTy)

bvbinary
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => (forall n. KnownPos n => SymBitVec n -> SymBitVec n -> SymBitVec n)
  -> EvalExpr es
bvbinary f = embed @BinBitVecOp emptySubst $ liftF3 \_n lhs rhs -> do
  SomeBitVec @nl lhs' <- lhs
  SomeBitVec @nr rhs' <- rhs
  Refl <- failWithE () $ eqT @nl @nr
  pure $ SomeBitVec (f lhs' rhs')

asSignedBin
  :: (forall n. KnownPos n => SymIntN n -> SymIntN n -> SymIntN n)
  -> (forall n. KnownPos n => SymBitVec n -> SymBitVec n -> SymBitVec n)
asSignedBin f = \lhs rhs -> do
  let lhs' = toSigned lhs
  let rhs' = toSigned rhs
  toUnsigned $ f lhs' rhs'

-- | Bitvector bitwise and.
bvand :: PrimOpExpr es
bvand = bvbinary (.&.)

-- | Bitvector bitwise or.
bvor :: PrimOpExpr es
bvor = bvbinary (.|.)

-- | Bitvector bitwise exclusive or.
bvxor :: PrimOpExpr es
bvxor = bvbinary Bits.xor

-- | Bitvector addition.
bvadd :: PrimOpExpr es
bvadd = bvbinary (+)

-- | Bitvector multiplication.
bvmul :: PrimOpExpr es
bvmul = bvbinary (*)

-- | Bitvector unsigned division.
bvudiv :: PrimOpExpr es
bvudiv = bvbinary div

-- | Bitvector signed division.
bvsdiv :: PrimOpExpr es
bvsdiv = bvbinary $ asSignedBin div
  
-- | Bitvector unsigned remainder.
bvurem :: PrimOpExpr es
bvurem = bvbinary rem

-- | Bitvector signed remainder.
bvsrem :: PrimOpExpr es
bvsrem = bvbinary $ asSignedBin rem

-- | Bitvector shift left.
bvshl :: PrimOpExpr es
bvshl = bvbinary symShift

-- | Bitvector logical shift right.
bvlshr :: PrimOpExpr es
bvlshr = bvbinary symShiftNegated

-- | Bitvector arithmetic shift right.
bvashr :: PrimOpExpr es
bvashr = bvbinary $ asSignedBin symShiftNegated

-- -- TODO: both bvrol and bvror are parametric over the shift amount more akin to
-- -- KnownNat. Perhaps it would be best to model them as such? This is also more
-- -- transparent to the user! I'll have to first maybe see what code exactly is
-- -- emitted by grisette when I want to do this in the first place.
-- bvrol :: PrimOpExpr es
-- bvrol = undefined

-- bvror :: PrimOpExpr es
-- bvror = undefined

type CompareBitVecOp
  =   Forall 0 NaturalTy
  :.  BitVecTy (TyVar 0 NaturalTy)
  :-> BitVecTy (TyVar 0 NaturalTy)
  :-> BoolTy

bvcompare
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  => (forall n. KnownPos n => SymBitVec n -> SymBitVec n -> SymBool)
  -> EvalExpr es
bvcompare f = embed @CompareBitVecOp emptySubst $ liftF3 \_ lhs rhs -> do
  SomeBitVec @nl lhs' <- lhs
  SomeBitVec @nr rhs' <- rhs
  Refl <- failWithE () $ eqT @nl @nr
  pure $ f lhs' rhs'

asSignedCmp
  :: (forall n. KnownPos n => SymIntN n -> SymIntN n -> SymBool)
  -> (forall n. KnownPos n => SymBitVec n -> SymBitVec n -> SymBool)
asSignedCmp f = \lhs rhs -> do
  let lhs' = toSigned lhs
  let rhs' = toSigned rhs
  f lhs' rhs'

bveq :: PrimOpExpr es
bveq = bvcompare (.==)

bvneq :: PrimOpExpr es
bvneq = bvcompare (./=)

bvule :: PrimOpExpr es
bvule = bvcompare (.<=)

bvsle :: PrimOpExpr es
bvsle = bvcompare $ asSignedCmp (.<=)

bvult :: PrimOpExpr es
bvult = bvcompare (.<)

bvslt :: PrimOpExpr es
bvslt = bvcompare $ asSignedCmp (.<)

type ConcatBitVecOp
  =   Forall 0 NaturalTy
  :.  Forall 1 NaturalTy
  :.  BitVecTy (TyVar 0 NaturalTy)
  :-> BitVecTy (TyVar 1 NaturalTy)
  :-> BitVecTy (TyVar 0 NaturalTy :+ TyVar 1 NaturalTy)

bvconcat :: PrimOpExpr es
bvconcat = embed @ConcatBitVecOp emptySubst $ liftF4 \_ _ lhs rhs -> do
  SomeBitVec @nl lhs' <- lhs
  SomeBitVec @nr rhs' <- rhs
  SomeNat' @n <- pure $ typeAdd @nl @nr
  -- SAFETY: Both bitvectors already have a positive bitwidth, thus their
  -- concatenation also has a positive bitwidth.
  Dict <- pure $ unsafeDict @(1 <= n)
  pure $ SomeBitVec (sizedBVConcat lhs' rhs')

-- :: forall idx width n
--  . KnownNat idx
-- => KnownNat width
-- => 0 <= width
-- => idx + width <= n
-- => BitVector n
-- -> BitVector width
type SelectBitVecOp
  =   Forall 0 NaturalTy
  :.  Forall 1 NaturalTy
  :.  Forall 2 NaturalTy
  :.  KnownNatTy (TyVar 0 NaturalTy)
  :-> KnownNatTy (TyVar 1 NaturalTy)
  :-> (Natural 0 :<= (TyVar 1 NaturalTy))
  :-> (TyVar 0 NaturalTy :+ TyVar 1 NaturalTy :<= TyVar 2 NaturalTy)
  :-> BitVecTy (TyVar 2 NaturalTy)
  :-> BitVecTy (TyVar 1 NaturalTy)

bvselect :: PrimOpExpr es
bvselect = embed @SelectBitVecOp emptySubst $ liftF8 \_ _ _ idx width _ _  bv -> do
  SomeNat @idx _ <- idx
  SomeNat @width _ <- width
  SomeBitVec @n bv' <- bv
  Dict <- failWithE () $ posNat @idx
  Dict <- failWithE () $ posNat @width
  SomeNat' @sum <- pure $ typeAdd @idx @width
  Dict <- failWithE () $ leqNat @sum @n
  pure $ SomeBitVec (sizedBVSelect (Proxy @idx) (Proxy @width) bv')

-- :: forall k v. Primitive k => Primitive v => v -> Array k v
type ArrayConstOp
  =   Forall 0 TypeKind
  :.  Forall 1 TypeKind
  :.  PrimitiveTy (TyVar 0 TypeKind)
  :-> PrimitiveTy (TyVar 1 TypeKind)
  :-> TyVar 1 TypeKind
  :-> ArrayTy (TyVar 0 TypeKind) (TyVar 1 TypeKind)

aconst :: PrimOpExpr es
aconst = embed @ArrayConstOp emptySubst $ liftF5 \_ _ pk _ valE -> do
  -- Gather constraints for primitive types.
  (_kco, SomeLiteralType @k kty) <- pk

  -- Gather the literal, knowing it is one due to the constraint.
  Literal @v vty val <- valE >>= \case
    Lit lit -> pure lit
    _ -> throwE ()

  -- Gather evidence required to perform the array operation.
  Dict <- pure $ evidence kty
  Dict <- pure $ evidence vty

  -- Create the constant array.
  let array = Array.const @k @v val
  pure $ SomeArray array

-- :: forall k v. Primitive k => Primitive v => Array k v -> k -> v
type ArraySelectOp
  =   Forall 0 TypeKind
  :.  Forall 1 TypeKind
  :.  PrimitiveTy (TyVar 0 TypeKind)
  :-> PrimitiveTy (TyVar 1 TypeKind)
  :-> ArrayTy (TyVar 0 TypeKind) (TyVar 1 TypeKind)
  :-> TyVar 0 TypeKind
  :-> TyVar 1 TypeKind

aselect :: PrimOpExpr es
aselect = embed @ArraySelectOp emptySubst $ liftF6 \_ _ _ _ arrE keyE -> do
  -- Get the inner array.
  SomeArray @k @v arr <- arrE

  -- Gather the literal, knowing it is one due to the constraint.
  Literal kty key <- keyE >>= \case
    Lit lit -> pure lit
    _ -> throwE ()

  -- Gather evidence required to perform the array operation.
  Refl <- failWithE () $ eqLiteralType (literalType @k) kty

  -- Select the value out of the array and wrap it back into an expression.
  let val = Literal (literalType @v) $ Array.select arr key
  pure $ mkLit val

-- :: forall k v. Primitive k => Primitive v => Array k v -> k -> v -> Array k v
type ArrayStoreOp
  =   Forall 0 TypeKind
  :.  Forall 1 TypeKind
  :.  PrimitiveTy (TyVar 0 TypeKind)
  :-> PrimitiveTy (TyVar 1 TypeKind)
  :-> ArrayTy (TyVar 0 TypeKind) (TyVar 1 TypeKind)
  :-> TyVar 0 TypeKind
  :-> TyVar 1 TypeKind
  :-> ArrayTy (TyVar 0 TypeKind) (TyVar 1 TypeKind)

astore :: PrimOpExpr es
astore = embed @ArrayStoreOp emptySubst $ liftF7 \_ _ _ _ arrE keyE valE -> do
  -- Get the inner array.
  SomeArray @k @v arr <- arrE

  -- Gather the literal, knowing it is one due to the constraint.
  Literal kty key <- keyE >>= \case
    Lit lit -> pure lit
    _ -> throwE ()

  -- Gather the literal, knowing it is one due to the constraint.
  Literal vty val <- valE >>= \case
    Lit lit -> pure lit
    _ -> throwE ()

  -- Gather evidence required to perform the array operation.
  Refl <- failWithE () $ eqLiteralType (literalType @k) kty
  Refl <- failWithE () $ eqLiteralType (literalType @v) vty

  -- Create the modified array.
  let array = Array.store arr key val
  pure $ SomeArray array
