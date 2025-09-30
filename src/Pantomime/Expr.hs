{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module Pantomime.Expr
  ( Eval (..)
  , Variant (..)
  , Expr (..)
  , Arg
  , Literal (..)
  , Type
  , Coercion

  , pprExpr
  , pprArg
  , pprEval

  , mkLit
  , mkDataCon
  , mkEnumCon
  , mkIntN
  , mkWordN
  , mkInteger
  , mkType
  , mkCoercion
  , mkLam
  , mkApp
  , mkApps
  , mkCastMCo
  , mkCast

  , mkUnreachable
  , mkUB
  , mkRaise

  , forceTyCo
  , forceTy
  , forceCo

  , exprToBool
  , eqType
  , eqLit
  , exprType
  , litType
  , concreteDataCon
  , collectArgs
  , collectScrut

  , throwE
  , failWithE
  , liftR
  , dbgE
  ) where

import GHC.Plugins qualified as GHC
import GHC.Core.Type qualified as GHC
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.Ppr (pprOptCo)
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Core.Opt.Arity (pushCoTyArg, pushCoValArg)
import GHC.Utils.Outputable
  ( Outputable (..)
  , IsLine (..)
  , SDoc
  , ($+$)
  , parens
  , hang
  , nest
  )
import GHC.Plugins
  ( Type
  , Coercion
  , CoercionR
  , MCoercionR
  , MCoercion (..)
  , Role (..)
  , TyCon
  , DataCon
  , HasCallStack
  , isEnumerationTyCon
  , dataConTagZ
  , dataConTyCon
  , isFunTy
  , isForAllTy
  , coercionRole
  , coercionLKind
  , isReflexiveCo
  , mkTransCo
  , coercionRKind
  , isCoVarType
  , mkCoCast
  , isForAllTy_ty
  , coercionType
  , splitFunTy_maybe
  , splitForAllTyCoVar_maybe
  , tyConDataCons
  , dataConRepType
  , mkCoercionTy
  , tyCoVarsOfTypes
  , mkInScopeSet
  , extendTCvSubst
  , splitTyConApp_maybe
  , dataConExTyCoVars
  , splitAtList
  , dropList
  , dataConUnivTyVars
  , decomposeCo
  , tyConArity
  , tyConRolesRepresentational
  , liftCoSubstWithEx
  , dataConRepArgTys
  , mkEmptySubst
  , boolTyCon
  , trueDataCon
  )

import GHC.TypeNats (KnownNat)
import GHC.Generics (Generic)

import Grisette.Unified (EvalModeTag (..))
import Grisette
  ( Union
  , SymBool
  , SymInteger
  , SymEq (..)
  , SymOrd (..)
  , LogicalOp ((.&&))
  , ToSym (..)
  , ToCon (..)
  , TryMerge (..)
  , Mergeable (..)
  , Mergeable1 (..)
  , SimpleMergeable (..)
  , SimpleMergeable1 (..)
  , SymBranching (..)
  , MergingStrategy (..)
  , EvalSym (..)
  , EvalSym1 (..)
  , Default (..)
  , wrapStrategy
  , rootStrategy1
  , liftUnion
  , mrgIf
  , pattern Single
  , pattern If
  )

import Pantomime.Orphan.GHC ()
import Pantomime.Result
import Pantomime.Grisette.SomeBV (SomeBV (..))
import Pantomime.Grisette.Mergeable
  ( NoMerge (..)
  , partialStrategy
  , ifStrategy
  , tupleStrategy
  , impossible
  )
import Pantomime.Grisette.BitVector
  ( IntN
  , WordN
  )

import Data.Composition ((.:))
import Data.Coerce (coerce)
import Data.List ((!?))
import Data.Traversable (for)
import Data.Typeable
  ( type (:~:) (..)
  , eqT
  )

import Control.Arrow (Arrow(..))
import Control.Applicative (Alternative(..))
import Control.Monad.Except
  ( ExceptT (..)
  , runExceptT
  )
import Control.Monad
  ( foldM
  , unless
  , (>=>)
  )

import Debug.Trace qualified as Debug

dbgE :: GHC.Outputable o => o -> Eval ()
dbgE m = Debug.trace (GHC.showSDocUnsafe $ GHC.ppr m) $ pure ()

-- TODO: I want to add plucky error values to Eval. We adjusted the error value
-- to use it internally, but have yet to expose it.
newtype Eval a where
  Eval ::
    -- TODO: I adjusted the order of errors here. I wonder if it is better to
    -- group errors all together like this, or linearly how we had it before.
    -- We should look into this both in terms of constraint size and solve
    -- duration. My guess is that this encoding is slightly less optimal for
    -- constraint size. Of course, this doesn't necessarily mean the solver is
    -- always faster.
    { runEval :: ExceptT (Result '[()] Variant) Union a
    } -> Eval a
  deriving Functor
  deriving Applicative
  deriving Monad

-- TODO: I feel like these instances are a bit messy here and distract from the
-- core data structures. Should we move these?
type MergeableEval = ExceptT (Either (NoMerge (Error '[()])) Variant) Union

instance Mergeable a => Mergeable (Eval a) where
  rootStrategy = rootStrategy1

instance Mergeable1 Eval where
  liftRootStrategy = coerce . liftRootStrategy @MergeableEval

instance Mergeable a => SimpleMergeable (Eval a) where
  mrgIte = coerce $ mrgIte @(MergeableEval a)

instance SimpleMergeable1 Eval where
  liftMrgIte @a = coerce $ liftMrgIte @MergeableEval @a

instance TryMerge Eval where
  tryMergeWithStrategy @a = coerce $ tryMergeWithStrategy @MergeableEval @a

instance SymBranching Eval where
  mrgIfWithStrategy @a = coerce $ mrgIfWithStrategy @MergeableEval @a

  mrgIfPropagatedStrategy @a = coerce $ mrgIfPropagatedStrategy @MergeableEval @a

-- TODO: Should this marker get it's own file?
newtype NoEval a where
  NoEval :: a -> NoEval a

instance EvalSym (NoEval a) where
  evalSym _ _ = id

type EvalSymEval = ExceptT (Either (NoEval (Error '[()])) Variant) Union

instance EvalSym a => EvalSym (Eval a) where
  evalSym = coerce $ evalSym @(EvalSymEval a)

instance EvalSym1 Eval where
  liftEvalSym @a = coerce $ liftEvalSym @(EvalSymEval) @a

-- TODO: I'm not sure if I like this name. Perhaps we can think about what other
-- options these have. Unlike the other error types, these ones don't need a
-- stack trace, as they're actually just valid values. In fact, I **really**
-- want these to merge! Perhaps something like NominalExcept/Error?
data Variant where
  UB :: Variant
  Unreachable :: Variant
  -- TODO: Should this not contain an Eval Expr? In any case, we haven't really
  -- implemented errors yet, so we should just look into this still.
  Raise :: Expr -> Variant
  deriving Generic
  deriving Mergeable via Default Variant
  deriving EvalSym via Default Variant

data Expr where
  Lit
    :: Literal
    -> Expr
  Type
    :: Type
    -> Expr
  Coercion
    :: Coercion
    -> Expr
  Lam
    :: Type
    -- ^ Expression type
    -> (Arg -> Eval Expr)
    -- ^ Closure
    -> Expr
  App
    :: Expr
    -> Thunk
    -> Expr
  Cast
    :: Union Expr
    -> CoercionR
    -> Expr
  deriving Generic
  deriving Mergeable via Default Expr

type Arg = Eval Expr

-- TODO: For now, I've made this Thunk so data constructors with different
-- existentials applications do not merge. I'm not sure whether perhaps it is
-- completely okay to let them merge btw, so we'd have to try this out. Perhaps
-- we can get rid of it.
--
-- Alternatively, we could write a custom merge strategy that will look at the
-- inner argument when it determines it should be a type or coercion.
--
-- Still, I'm somewhat convinced that we actually might just optimise error
-- branches (that occurred due to existentials) away. If this is true, I feel
-- like universal type arguments should perhaps just be part of the DataCon
-- literal. Then we can get rid of this thunk data type.
--
-- Note that one thing that happens with this is that at some time during eval
-- we might get a Union of expressions with different types. Not sure how to
-- feel about that...
--
-- After Tests:
---------------
-- We indeed reduce the bad branches away. I'm not sure about what would be the
-- best in terms of raw evaluation speed. This version requires an evaluation
-- of the right hand side of a case for every existential instance. This seems
-- somewhat unwanted.
--
-- The alternative is to have an (Eval TvSubstEnv) and (Eval CvSubstEnv) inside
-- of our Subst. Then at usage site we will have the errors in the leaves
-- instead. I feel like this is better, but idk. There is really only one way to
-- find out, which is to actually evaluate it.
--
-- Unwrapping the Eval Type outside of the TvSubstEnv is definitely not the
-- right move though. In this case, we may run many more branches than required
-- as we run a permutation of every possible pair of existential types (even
-- pairs that will not exist) for the entire rhs. In other words, we will
-- possibly run many more instances if we allow existential types to merge
-- without wrapping the substitition environment inside of Eval.
--
-- Having it inside means that we will run the
-- error branches where the existential is actually used.
--
-- NOTE on existentials:
-- If we are to fully put the universal and existential arguments in the
-- DataCon, then remember the following: the existential field only needs to be
-- of type [Type]. This feels counter-intuitive since the existential variables
-- field is of type TyCoVar. Still, this is correct. Coercions should simply be
-- wrapped via the use of mkCoercionTy. It took me a long time to figure this
-- out, so I wrote it down here!
data Thunk where
  Thunked :: Arg -> Thunk
  Forced :: Either Type Coercion -> Thunk
  deriving Generic
  deriving Mergeable via Default Thunk

data Literal where
  -- TODO: I think it makes sense to place the universal type arguments of a
  -- DataCon inside of the literal.
  DataCon
    :: KnownNat n
    => IntN S n
    -> TyCon
    -> Literal
  Int
    :: KnownNat n
    => IntN S n
    -> Type
    -> Literal
  Word
    :: KnownNat n
    => WordN S n
    -> Type
    -> Literal
  Integer
    :: SymInteger
    -> Type
    -> Literal

instance Mergeable Literal where
  rootStrategy = SortedStrategy
    (\case
      DataCon _ _ -> 0 :: Int
      Int _ _ -> 1
      Word _ _ -> 2
      Integer _ _ -> 3)
    \case
      0 -> wrapStrategy
        (ifStrategy
          (isEnumerationTyCon . snd)
          -- If this is an enumeration TyCon, we can simply merge the tags
          -- as all DataCon have the same type.
          rootStrategy
          -- If this is not an enumeration TyCon, we cannot merge tags as the
          -- DataCon have different types. Thus, we use a concrete strategy.
          -- This means, only exactly equivalent concrete tags are merged.
          -- No merging will occur if the tag is symbolic. A symbolic tag for
          -- a non-enumeration DataCon is considered as inconsistent.
          (tupleStrategy
            (partialStrategy @(SomeBV (IntN C)) toSym toCon rootStrategy)
            rootStrategy))
        (\case (SomeBV tag, tc) -> DataCon tag tc)
        \case DataCon tag tc -> (SomeBV tag, tc) ; _ -> impossible

      1 -> wrapStrategy
        rootStrategy
        (\case (SomeBV value, ty) -> Int value ty)
        \case Int value ty -> (SomeBV value, ty) ; _ -> impossible

      2 -> wrapStrategy
        rootStrategy
        (\case (SomeBV value, ty) -> Word value ty)
        \case Word value ty -> (SomeBV value, ty) ; _ -> impossible

      3 -> wrapStrategy
        rootStrategy
        (\case (value, ty) -> Integer value ty)
        \case Integer value ty -> (value, ty) ; _ -> impossible

      _ -> impossible

instance EvalSym Expr where
  evalSym fill model = \case
    Lit lit -> Lit $ evalSym' lit
    Type ty -> Type ty
    Coercion co -> Coercion co
    Lam ty closure -> Lam ty \arg -> evalSym' (closure arg)
    App fun arg -> App (evalSym' fun) (evalSym' arg)
    Cast body co -> Cast (evalSym' body) co
    where
      evalSym' :: EvalSym a => a -> a
      evalSym' = evalSym fill model

instance EvalSym Literal where
  evalSym fill model = \case
    DataCon tag tc -> DataCon (evalSym' tag) tc
    Int value ty -> Int (evalSym' value) ty
    Word value ty -> Word (evalSym' value) ty
    Integer value ty -> Integer (evalSym' value) ty
    where
      evalSym' :: EvalSym a => a -> a
      evalSym' = evalSym fill model

instance EvalSym Thunk where
  evalSym fill model = \case
    Thunked value -> Thunked $ evalSym fill model value
    Forced value -> Forced value

pprExpr
  :: (SDoc -> SDoc)
  -> Expr
  -> SDoc
pprExpr addParens = \case
  Lit lit -> ppr lit
  Type ty -> "@" GHC.<> ppr ty
  Coercion co -> "@~" GHC.<> ppr co
  Cast expr co -> addParens $ sep
    [ pprUnion parens pprExpr expr
    , "`cast`" <+> pprOptCo co
    ]
  Lam {} -> "TODO lambda"
    -- (result, args) <- saturateLam @64 $ mkExpr expr
    -- let bndrs = fst <$> args
    -- let bndr = "\\" <+> sep (ppr <$> bndrs) <+> GHC.arrow
    -- body <- pprExpr id result
    -- pure . addParens $ hang bndr 2 body
  expr@App {} -> do
    let (fun, args) = collectArgs expr
    -- args' <- sequenceA args
    -- args'' <- for args' $ pprExpr parens
    let header = pprExpr parens fun
    let body = sep $ pprArg parens <$> args
    addParens $ hang header 2 body

pprArg
  :: (SDoc -> SDoc)
  -> Arg
  -> SDoc
pprArg addParens = pprEval addParens pprExpr

pprEval
  :: forall a
   . Mergeable a
  => (SDoc -> SDoc)
  -> ((SDoc -> SDoc) -> a -> SDoc)
  -> Eval a
  -> SDoc
pprEval addParens f m = do
  let inner p = \case
        Left (Left _err) -> undefined -- "UNKNOWN ERROR :(" $+$ text (prettyCallStack trace)
        Left (Right UB) -> "UB"
        Left (Right Unreachable) -> "Unreachable"
        Left (Right (Raise expr)) -> "raise#" <+> pprExpr p expr
        Right expr -> f p expr

  let m' = runExceptT $ coerce @_ @(MergeableEval a) m
  pprUnion addParens inner m'

pprUnion
  :: Mergeable a
  => (SDoc -> SDoc)
  -> ((SDoc -> SDoc) -> a -> SDoc)
  -> Union a
  -> SDoc
pprUnion addParens inner = \case
  Single value -> inner addParens value
  If scrut true false -> do
    -- Vertically concatenate using ($+$).
    let vcat' = foldl' @[] ($+$) GHC.empty

    -- Hang that always aligns vertically.
    let hang' d1 n d2 = vcat' [d1, nest n d2]

    addParens . hang' "ite" 2 $ vcat'
      [ text $ show scrut
      , pprUnion parens inner true
      , pprUnion parens inner false
      ]

-- TODO: I don't like this too much, ideally it is polymorphic over any Expr,
-- but I don't now how to properly parenthesise an Expr in this case (as
-- the inner expression needs to get a function which parenthesises it, if
-- necessary).
instance Outputable (Eval Expr) where
  ppr = pprArg id

instance Outputable Expr where
  ppr = pprExpr id

instance Outputable Literal where
  ppr = \case
    -- TODO: This should output the tag directly if concrete. If not and this is
    -- an enumeration TyCon, we should emit a tagToEnum# apply to the value. If
    -- this is not an enumeration TyCon, then the tag is invalid. We should
    -- probably print some sort of error message in that case.
    DataCon @n tag tc
      | Just tag' <- toCon @_ @(IntN C n) tag 
      , Just dc <- tyConDataCons tc !? fromIntegral tag' -> ppr dc
      -- TODO: Technically this print is wrong as the type application should be
      -- the whole type, not just the TyCon.
      | isEnumerationTyCon tc -> "tagToEnum#" <+> "@" GHC.<> ppr tc <+> ppr (SomeBV tag)
      | otherwise -> "INVALID DATACON"
    Int value ty -> ppr (SomeBV value) <+> "::" <+> ppr ty
    Word value ty -> ppr (SomeBV value) <+> "::" <+> ppr ty
    Integer value ty -> text (show value) <+> "::" <+> ppr ty

mkLit
  :: Literal
  -> Expr
mkLit = Lit

mkDataCon
  :: forall n
   . KnownNat n
  => DataCon
  -> Literal
mkDataCon dc = do
  let tag = fromIntegral . dataConTagZ $ dc
  let tc = dataConTyCon dc
  DataCon @n tag tc

mkEnumCon
  :: forall n
   . KnownNat n
  => IntN S n
  -> Type
  -> Eval Expr
mkEnumCon tag ty = do
  -- Ensure we have an enumeration type.
  (tc, targs) <- failWithE () $ splitTyConApp_maybe ty
  unless (isEnumerationTyCon tc) do
    throwE ()

  -- Construct the data constructor and its type arguments.
  let dc = mkLit $ DataCon tag tc
  let targs' = pure . mkType <$> targs
  mkApps dc targs'

mkIntN
  :: KnownNat n
  => IntN S n
  -> Type
  -> Literal
mkIntN = Int

mkWordN
  :: KnownNat n
  => WordN S n
  -> Type
  -> Literal
mkWordN = Word

mkInteger
  :: SymInteger
  -> Type
  -> Literal
mkInteger = Integer

mkType
  :: Type
  -> Expr
mkType = Type

mkCoercion
  :: Coercion
  -> Expr
mkCoercion co = Coercion co

mkLam
  :: Type
  -> (Arg -> Eval Expr)
  -> Expr
mkLam = Lam

mkApp
  :: HasCallStack
  => Expr
  -> Arg
  -> Eval Expr
mkApp fun arg = case fun of
  Cast body co -> do
    (arg', rco) <- pushCoArg co arg
    body' <- liftUnion body
    expr <- mkApp body' arg'
    mkCastMCo expr rco
  Lam _ty closure -> closure arg
  _ -> do
    ty <- liftR $ exprType fun
    if
      | isFunTy ty -> pure $ App fun (Thunked arg)
      | isForAllTy ty -> do
        forced <- liftR $ forceTyCo arg
        pure $ App fun (Forced forced)
      | otherwise -> throwE ()

pushCoArg
  :: HasCallStack
  => CoercionR
  -> Arg
  -> Eval (Arg, MCoercionR)
pushCoArg co arg = if
  | tyL <- coercionLKind co
  , isForAllTy_ty tyL -> do
    -- The argument needs to be a type. As such, we can force it.
    ty <- liftR $ forceTy arg

    -- Attempt to push the coercion into the type argument.
    (ty', rco) <- failWithE () $ pushCoTyArg co ty

    -- Return the type argument and result coercion.
    pure (pure $ mkType ty', rco)

  | otherwise -> do
    -- Attempt to split the coercion into an argument and result coercion.
    (aco, rco) <- failWithE () $ pushCoValArg co

    -- Cast the argument and return the result coercion.
    let arg' = arg >>= flip mkCastMCo aco
    pure (arg', rco)

mkApps
  :: Expr
  -> [Arg]
  -> Eval Expr
mkApps = foldM mkApp

mkCastMCo
  :: HasCallStack
  => Expr
  -> MCoercionR
  -> Eval Expr
mkCastMCo expr = \case
  MRefl -> pure expr
  MCo co -> mkCast expr co

mkCast
  :: HasCallStack
  => Expr
  -> CoercionR
  -> Eval Expr
mkCast expr co = do
  -- Ensure the coercion has role representational.
  unless (coercionRole co == Representational) do
    -- FIXME: Make this a proper error.
    throwE ()

  -- Ensure the cast can be applied to the expression.
  ty <- liftR $ exprType expr
  unless (eqType ty $ coercionLKind co) do
    -- FIXME: Make this a proper error.
    throwE ()

  case expr of
    -- A reflexive cast is a no-op and thus may be removed immediately.
    _ | isReflexiveCo co -> pure expr

    -- TODO: This is a recursive call of HasCallStack, I should capture it in a
    -- closure as to not blow it up instead!
    Cast body co' -> do
      body' <- liftUnion body
      mkCast body' $ mkTransCo co' co

    -- NOTE: This comment was written originally inside of GHC 'mkCast'. I'm
    -- unsure what 'g' refers to (it's not in the original code either), but
    -- I'll keep the guard check here as it is probably important.
    --
    -- ```
    -- The guard here checks that g has a (~#) on both sides, otherwise
    -- 'decomposeCo' fails. Can in principle happen with unsafeCoerce.
    -- ```
    Coercion co' | isCoVarType $ coercionRKind co -> do
      pure $ mkCoercion (mkCoCast co' co)

    _ -> pure $ Cast (pure expr) co

mkVariant
  :: Variant
  -> Eval a
mkVariant = Eval . ExceptT . pure . Left . Right

mkUnreachable :: Eval a
mkUnreachable = mkVariant Unreachable

mkUB :: Eval a
mkUB = mkVariant UB

mkRaise :: Expr -> Eval a
mkRaise = mkVariant . Raise

-- | Force an expression into a type or coercion.
--
-- A type or coercion is always terminating. Within a union they should
-- additionally always be a single. As such, we can escape the monad here.
--
-- WARNING: In general, expressions may be non-terminating. Use only when a Type
-- or Coercion is the expected result.
forceTyCo
  :: HasCallStack
  => () !> es
  => Arg
  -> Result es (Either Type Coercion)
forceTyCo arg = case runExceptT $ coerce @_ @(MergeableEval Expr) arg of
  -- TODO: Should we throw the original error if an Error occurs inside of
  -- here? This kind of masks the origin of an error here!
  Single (Right value) -> case value of
    Type ty -> pure $ Left ty
    Coercion co -> pure $ Right co
    _ -> throw ()
  _ -> throw ()

forceTy
  :: HasCallStack
  => () !> es
  => Arg
  -> Result es Type
forceTy = forceTyCo >=> either pure (const $ throw ())

forceCo
  :: HasCallStack
  => () !> es
  => Arg
  -> Result es Coercion
forceCo = forceTyCo >=> either (const $ throw ()) pure

-- | Convert an expression of type Bool to a symbolic boolean.
exprToBool
  :: Expr
  -> Eval SymBool
exprToBool = \case
  Lit (DataCon tag tc) | tc == boolTyCon -> do
    -- The bounds of the tag.
    let upper = fromIntegral $ length (tyConDataCons tc)
    let inBounds = 0 .<= tag .&& tag .< upper

    let trueTag = fromIntegral $ dataConTagZ trueDataCon
    let result = pure $ tag .== trueTag

    mrgIf inBounds result mkUB
  _ -> throwE ()

-- | Equivalence between literals.
--
-- NOTE: This only handles cases that may occur in a case expression.
eqLit
  :: () !> es
  => Literal
  -> Literal
  -> Result es SymBool
eqLit = \cases
  (DataCon @l ltag ltc) (DataCon @r rtag rtc) 
    | ltc == rtc
    , Just Refl <- eqT @l @r -> pure $ ltag .== rtag
  (Int @l lval lty) (Int @r rval rty) 
    | eqType lty rty
    , Just Refl <- eqT @l @r -> pure $ lval .== rval
  (Word @l lval lty) (Word @r rval rty) 
    | eqType lty rty
    , Just Refl <- eqT @l @r -> pure $ lval .== rval
  _ _ -> throw ()

-- TODO: I split away the Eval from this as I'm only using the error. I don't
-- like the monad error constraint too much though, so I want to find a better
-- solution sometime.
exprType
  :: HasCallStack
  => () !> es
  => Expr
  -> Result es Type
exprType = \case
  Lit lit -> litType lit
  Type _ -> throw ()
  Coercion co -> pure $ coercionType co
  Lam ty _ -> pure ty
  App fun arg -> do
    -- TODO: Recursive call grows callstack, fix this!
    fty <- exprType fun
    if
      | Just (var, rty) <- splitForAllTyCoVar_maybe fty -> do
        aty <- case arg of
          Forced (Right co) -> pure $ mkCoercionTy co
          Forced (Left ty) -> pure ty
          _ -> throw ()
        let scope = mkInScopeSet $ tyCoVarsOfTypes [aty, rty]
        let subst = extendTCvSubst (mkEmptySubst scope) var aty
        pure $ GHC.substTy subst rty

      | Just (_, _, _, rty) <- splitFunTy_maybe fty -> pure rty

      | otherwise -> throw ()
  Cast _ co -> pure $ coercionRKind co

litType
  :: () !> es
  => Literal
  -> Result es Type
litType = \case
  DataCon tag tc -> do
    dc <- failWith () $ anyDataCon tag tc
    pure $ dataConRepType dc
  Int _ ty -> pure ty
  Word _ ty -> pure ty
  Integer _ ty -> pure ty

-- | Attempts to concretise a tag to a DataCon. If the TyCon is an enumeration,
-- this will as a back-up gather any DataCon.
--
-- Enumeration tags may not be concretisable as they can be instantiated via
-- arithmetic. As all DataCon in the enumeration have the same type, it may
-- still be useful to fetch it.
anyDataCon
  :: forall n
   . KnownNat n
  => IntN S n
  -> TyCon
  -> Maybe DataCon
anyDataCon tag tc = do
  let dcs = tyConDataCons tc
  concreteDataCon tag tc <|> if
    -- Enumeration TyCon all have the same type, so we just select the first
    -- one. Note that it could be impossible to get a concrete DataCon here,
    -- as enumeration DataCon can be created from an arithmetic expression.
    | isEnumerationTyCon tc
    , dc : _ <- dcs -> pure dc
    | otherwise -> empty

-- | Attempts to concretise a tag to a DataCon.
concreteDataCon
  :: forall n
   . KnownNat n
  => IntN S n
  -> TyCon
  -> Maybe DataCon
concreteDataCon tag tc = do
  let dcs = tyConDataCons tc
  tag' <- toCon @_ @(IntN C n) tag 
  dcs !? fromIntegral tag'

-- | Collect the arguments of an application.
collectArgs
  :: Expr
  -> (Expr, [Arg])
collectArgs = second (fmap unthunk) . collectThunks

-- | Collect the thunks of an application.
collectThunks
  :: Expr
  -> (Expr, [Thunk])
collectThunks = go []
  where
    go args = \case
      App fun arg -> go (arg: args) fun
      expr -> (expr, args)

-- | Transform thunks into arguments.
--
-- Really, args are just always thunks. This will put forced values into thunks.
unthunk
  :: Thunk
  -> Arg
unthunk = \case
  Thunked value -> value
  Forced value -> case value of
    Right co -> pure $ mkCoercion co
    Left ty -> pure $ mkType ty

-- | Collect the arguments of a scrutinee.
--
-- This will drop any universal type applications as these are not necessary for
-- pattern matching. Additionally, this will push a TyCon Coercion into the
-- arguments of a DataCon if possible.
collectScrut
  :: Expr
  -> Eval (Literal, [Arg])
collectScrut = \case
  -- On a cast, we may attempt to push a TyConAppCo into the arguments of
  -- a DataCon literal.
  Cast body co -> do
    -- Perform the operation for every body in the cast.
    body' <- liftUnion body

    -- Collect the arguments and literal.
    (lit, args) <- case collectThunks body' of
      (Lit lit, args) -> pure (lit, args)
      _ -> throwE ()

    -- Only a DataCon may have its arguments pushed.
    dc <- case lit of
      DataCon tag tc | Just dc <- anyDataCon tag tc -> pure dc
      _ -> throwE ()

    -- Push the coercion into the arguments.
    (_univ, args') <- liftR $ pushCoDataCon dc args co
    pure (lit, unthunk <$> args')

  -- If not a cast, we attempt to get the literal at the spine and return the
  -- arguments excluding the universal type arguments.
  expr -> do
    -- Gather a literal and it's arguments if possible.
    (lit, args) <- case collectArgs expr of
      (Lit lit, args) -> pure (lit, args)
      _ -> throwE ()

    -- Find the number of universal arguments required for the literal.
    let univ = case lit of
          DataCon _ tc -> tyConArity tc
          Int {} -> 0
          Word {} -> 0
          Integer {} -> 0

    -- Drop the universal arguments and return.
    pure (lit, drop univ args)

-- | Push a TyConAppCo into the arguments of a DataCon.
pushCoDataCon
  :: HasCallStack
  => () !> es
  => DataCon
  -> [Thunk]
  -> Coercion
  -> Result es ([Type], [Thunk])
pushCoDataCon dc args co = do
  -- Check whether the outer type is a TyConAppCo.
  let tyR = coercionRKind co
  (tcR, univArgsR) <- failWith () $ splitTyConApp_maybe tyR
  unless (tcR == dataConTyCon dc) do
    throw ()

  -- Gather information on type variables of the DataCon.
  let dcUnivVars = dataConUnivTyVars dc
  let dcExVars = dataConExTyCoVars dc

  -- Get the existential and value arguments.
  (exTys, valArgs) <- do
    let (exArgs, valArgs) = splitAtList dcExVars $ dropList dcUnivVars args
    exTys <- for exArgs \case
      -- TODO: Do we need to wrap Coercions with mkCoercionTy?
      Forced (Left ty) -> pure ty
      _ -> throw ()
    valArgs' <- for valArgs \case
      Thunked value -> pure value
      Forced _ -> throw ()
    pure (exTys, valArgs')

  -- Get coercions for the universal type variables.
  let univCo = decomposeCo (tyConArity tcR) co $ tyConRolesRepresentational tcR

  -- Create the new existential type arguments and the type substitution for
  -- the argument casts.
  let (psiSubst, exTys')
        = liftCoSubstWithEx Representational dcUnivVars univCo dcExVars exTys

  -- Cast all the value arguments using the substitution.
  let argTys = scaledThing <$> dataConRepArgTys dc
  let castArg arg ty = arg >>= flip mkCast (psiSubst ty)
  let valArgs' = Thunked <$> zipWith castArg valArgs argTys

  -- Wrap the existential type arguments back into thunks.
  let exArgs = Forced . Left <$> exTys'

  pure (univArgsR, exArgs ++ valArgs')

-- TODO: This is horrible. It's better than not having a callstack, but we
-- should really improve the error handling to contain actual error values.
-- Also, we should probably freeze the callstack after this point.
throwE
  :: HasCallStack
--   => e !> es
--   => e
  => ()
  -> Eval a
throwE = Eval . ExceptT . pure . Left . throw

-- TODO: The callstack should probably be frozen before calling the throw.
failWithE
  :: HasCallStack
--   => e !> es
--   => e
  => ()
  -> Maybe a
  -> Eval a
failWithE = liftR .: failWith

-- | Lift a result into the evaluation context.
-- TODO: Allow more than just the unit error to be lifted once Eval support more
-- error types.
liftR :: Result '[()] a -> Eval a
liftR = \case
  Left err -> Eval . ExceptT . pure . Left . Left $ err
  Right value -> pure value
