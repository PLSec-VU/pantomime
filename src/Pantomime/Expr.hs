{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module Pantomime.Expr
  ( Eval (..)
  , Variant (..)
  , Expr (..)
  , EvalExpr
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
  , boolTyCon
  )

import GHC.TypeNats (KnownNat, SomeNat (..))
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack, withFrozenCallStack)

import Grisette.Unified (EvalModeTag (..))
import Grisette
  ( Union
  , SymBool
  , SymInteger
  , SymEq (..)
  , SymOrd (..)
  , LogicalOp ((.&&))
  , BitCast (..)
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
  , evalSym1
  , pattern Single
  , pattern If
  , pattern Con
  )

import Pantomime.Orphan.Grisette ()
import Pantomime.Orphan.GHC ()
import Pantomime.Result
import Pantomime.Grisette.SomeBV (SomeBV (..))
import Pantomime.Grisette.SizedBV (sizedBVResizeZ)
import Pantomime.Grisette.Mergeable
  ( partialStrategy
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
  , Proxy (..)
  , eqT
  )

import Control.Arrow (Arrow(..))
import Control.Applicative (Alternative(..), liftA)
import Control.Monad.Except
  ( ExceptT (..)
  , runExceptT
  )
import Control.Monad
  ( (>=>)
  , foldM
  , unless
  , join
  , ap
  )

import Debug.Trace qualified as Debug

-- TODO: This should be removed at some point? Or perhaps it's usage should
-- give an error? Idk, it is a really nice utility to have when debugging stuff.
dbgE :: GHC.Outputable o => o -> Eval es ()
dbgE m = Debug.trace (GHC.showSDocUnsafe $ GHC.ppr m) $ pure ()

newtype Eval es a where
  Eval :: EvalCoerce es a -> Eval es a

-- | Inner value of 'Eval' monad, which is useful as a shorthand when writing
-- coercions.
type EvalCoerce es a = Result es (ExceptT (Variant es) Union a)

instance Functor (Eval es) where
  fmap = liftA

instance Applicative (Eval es) where
  (<*>) = ap
  pure = Eval . Right . pure

-- TODO: I'm using an orphan implementation for Traversable on Union. Should
-- I just make a pull requist for it's implementation at this point?
instance Monad (Eval es) where
  (>>=) @a @b = coerce go
    where
      go :: EvalCoerce es a -> (a -> EvalCoerce es b) -> EvalCoerce es b
      go m f = do
        union <- m
        fmap join $ for union f

instance TryMerge (Eval es) where
  tryMergeWithStrategy @a strategy = coerce go
    where
      go :: EvalCoerce es a -> EvalCoerce es a
      go = fmap $ tryMergeWithStrategy strategy

instance Mergeable a => Mergeable (Eval es a) where
  rootStrategy = rootStrategy1

instance Mergeable1 (Eval es) where
  liftRootStrategy = SimpleStrategy . mrgIfWithStrategy

instance Mergeable a => SimpleMergeable (Eval es a) where
  mrgIte = mrgIf

instance SimpleMergeable1 (Eval es) where
  liftMrgIte = mrgIfWithStrategy . SimpleStrategy

-- WARNING: The implementation of symbolic branching for 'Eval' is very nuanced,
-- careless changes could harm how expressions are merged.
--
-- There are two slightly conflicting requirements on the 'Eval' monad.
-- 1. If any branch gives an error, we just want to kill the entire computation.
--    That is, there is no real reason to track the full union of values anymore
--    if an error occurred.
-- 2. We need expressions to be lazily evaluated and lazily merged, such that
--    it follows Haskell's evaluation semantic exactly.
--    - For lazy evaluation: Branches that remain unevaluated thus should
--      not propagate their errors. If they did, we would actually still
--      be evaluating (most of) the branch making it so we cannot evaluate
--      (bounded) recursive expressions.
--    - For lazy merging: For merging to be lazy, 'Arg' needs to implement
--      'SimpleMergeable'. Otherwise, we would be evaluating the entire
--      expression to sort the arguments when merging. Since 'Expr' is really
--      only 'Mergeable', we require 'Eval' to implement 'SymBranching'. Note
--      that it is also much more effecient for the constraint general if the
--      arguments are simple mergeable.
--
-- How do we resolve this conflict?
-- - We disregard branches that are never used, i.e. when the branch condition
--   is a concrete value. This ensure we retain the lazy semantic.
--
-- - When we do require merging, we will first ensure both branches are void of
--   any errors before merging the inner value.
--
-- - In the case there is at least one error, it is an arbitrary decision which
--   error to propagate. We choose to propagate the error of the then-branch
--   over that of the else-branch, but either way is fine. Alternatively, we
--   could choose to collect the errors from all branches instead of selecting
--   an arbitrary one. For now, selecting one seems reasonable.
instance SymBranching (Eval es) where
  mrgIfWithStrategy @a strategy scrut true false = case scrut of
    Con scrut'
      -- NOTE: We want to specifically use the TryMerge instance of Eval here
      -- (and not of EvalCoerce) as this one properly passes the strategy to the
      -- inner Union.
      | scrut' -> tryMergeWithStrategy strategy true
      | otherwise -> tryMergeWithStrategy strategy false
    _ -> coerce go true false
    where
      go :: EvalCoerce es a -> EvalCoerce es a -> EvalCoerce es a
      go = liftA2 $ mrgIfWithStrategy strategy scrut

  mrgIfPropagatedStrategy @a scrut = coerce go
    where
      go :: EvalCoerce es a -> EvalCoerce es a -> EvalCoerce es a
      go true false = case scrut of
        Con scrut'
          | scrut' -> true
          | otherwise -> false
        _ -> liftA2 (mrgIfPropagatedStrategy scrut) true false

instance EvalSym a => EvalSym (Eval es a) where
  evalSym = evalSym1

instance EvalSym1 (Eval es) where
  liftEvalSym @a f fill model = coerce go
    where
      go :: EvalCoerce es a -> EvalCoerce es a
      go = fmap $ liftEvalSym f fill model

-- TODO: I'm not sure if I like this name. Perhaps we can think about what other
-- options these have. Unlike the other error types, these ones don't need a
-- stack trace, as they're actually just valid values. In fact, I **really**
-- want these to merge! Perhaps something like NominalExcept/Error?
data Variant es where
  UB :: Variant es
  Unreachable :: Variant es
  -- TODO: Should this not contain an Eval Expr? In any case, we haven't really
  -- implemented errors yet, so we should just look into this still.
  Raise :: Expr es -> Variant es
  deriving Generic
  deriving Mergeable via Default (Variant es)
  deriving EvalSym via Default (Variant es)

data Expr es where
  Lit
    :: Literal
    -> Expr es
  Type
    :: Type
    -> Expr es
  Coercion
    :: Coercion
    -> Expr es
  Lam
    :: Type
    -- ^ Expression type
    -> (Arg es -> EvalExpr es)
    -- ^ Closure
    -> Expr es
  App
    :: Expr es
    -> Thunk es
    -> Expr es
  Cast
    :: Union (Expr es)
    -> CoercionR
    -> Expr es
  deriving Generic
  deriving Mergeable via Default (Expr es)

-- | Expressions within the evaluation context. You may also think of these as
-- thunks. It is expected that the spine of this expression is never a 'Type' or
-- 'Coercion'.
type EvalExpr es = Eval es (Expr es)

-- | Like 'EvalExpr', this may be considered a thunk. Unlike 'EvalExpr', this is
-- an expression that may appear in the argument position. This entails that
-- it may be a 'Type' or 'Coercion' in the spine.
type Arg es = EvalExpr es

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
data Thunk es where
  Thunked :: Arg es -> Thunk es
  Forced :: Either Type Coercion -> Thunk es
  deriving Generic
  deriving Mergeable via Default (Thunk es)

data Literal where
  -- TODO: I think it makes sense to place the universal type arguments of a
  -- DataCon inside of the literal.
  DataCon
    :: KnownNat n
    => IntN S n
    -> TyCon
    -> Literal
  -- TODO: Does it make sense to differentiate between IntN and WordN? I think
  -- the solver just has a single bitvector. This just seems like it adds
  -- maintanence burden without actually adding anything...
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

instance EvalSym (Expr es) where
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

instance EvalSym (Thunk es) where
  evalSym fill model = \case
    Thunked value -> Thunked $ evalSym fill model value
    Forced value -> Forced value

pprExpr
  :: (SDoc -> SDoc)
  -> Expr es
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
  -> Arg es
  -> SDoc
pprArg addParens = pprEval addParens pprExpr

pprEval
  :: forall a es
   . Mergeable a
  => (SDoc -> SDoc)
  -> ((SDoc -> SDoc) -> a -> SDoc)
  -> Eval es a
  -> SDoc
pprEval addParens f = coerce go
  where
    go :: EvalCoerce es a -> SDoc
    go = \case
      -- TODO: How should I actually emit the error...
      Left err -> GHC.prettyCallStackDoc $ location err
      -- TODO: This has a bit too much nesting for me, I should reduce it!
      Right union -> flip (pprUnion addParens) (runExceptT union) \p -> \case
        Left UB -> "UB"
        Left Unreachable -> "Unreachable"
        Left (Raise expr) -> "raise#" <+> pprExpr p expr
        Right expr -> f p expr

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
instance Outputable (EvalExpr es) where
  ppr = pprArg id

instance Outputable (Expr es) where
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
  -> Expr es
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
  :: forall n es
   . KnownNat n
  => () !> es
  => IntN S n
  -> Type
  -> EvalExpr es
mkEnumCon tag ty = do
  -- Ensure we have an enumeration type.
  (tc, targs) <- failWithE () $ splitTyConApp_maybe ty
  unless (isEnumerationTyCon tc) do
    throwE ()

  -- Check to ensure we have a proper tag.
  let upper = fromIntegral $ length (tyConDataCons boolTyCon)
  let inBounds = 0 .<= tag .&& tag .< upper

  -- Construct the data constructor and its type arguments.
  let dc = mkLit $ DataCon tag tc
  let targs' = pure . mkType <$> targs
  let expr = mkApps dc targs'

  -- The expression is UB if it the tag is not within bounds.
  mrgIf inBounds expr mkUB

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
  -> Expr es
mkType = Type

mkCoercion
  :: Coercion
  -> Expr es
mkCoercion = Coercion

mkLam
  :: Type
  -> (Arg es -> EvalExpr es)
  -> Expr es
mkLam = Lam

mkApp
  :: HasCallStack
  => () !> es
  => Expr es
  -> Arg es
  -> EvalExpr es
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
  => () !> es
  => CoercionR
  -> Arg es
  -> Eval es (Arg es, MCoercionR)
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
  :: HasCallStack
  => () !> es
  => Expr es
  -> [Arg es]
  -> EvalExpr es
mkApps = foldM mkApp

mkCastMCo
  :: HasCallStack
  => () !> es
  => Expr es
  -> MCoercionR
  -> EvalExpr es
mkCastMCo expr = \case
  MRefl -> pure expr
  MCo co -> mkCast expr co

mkCast
  :: HasCallStack
  => () !> es
  => Expr es
  -> CoercionR
  -> EvalExpr es
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

mkVariant :: Variant es -> Eval es a
mkVariant = Eval . pure . ExceptT . pure . Left

mkUnreachable :: Eval es a
mkUnreachable = mkVariant Unreachable

mkUB :: Eval es a
mkUB = mkVariant UB

mkRaise :: Expr es -> Eval es a
mkRaise = mkVariant . Raise

-- | Force an expression into a type or coercion.
--
-- A type or coercion is always terminating. Within a union they should
-- additionally always be a single. As such, we can escape the monad here.
--
-- WARNING: In general, expressions may be non-terminating. Use only when a Type
-- or Coercion is the expected result.
forceTyCo
  :: forall es
   . HasCallStack
  => () !> es
  => Arg es
  -> Result es (Either Type Coercion)
forceTyCo (Eval arg) = do
  -- Simply pass an already existing error, if possible.
  arg' <- arg

  case runExceptT arg' of
    -- Attempt to get a single 'Type' or 'Coercion'.
    Single (Right value)
      | Type ty <- value -> pure $ Left ty
      | Coercion co <- value -> pure $ Right co

    -- The expression was not in the expected shape.
    _ -> throw ()

-- | Force an expression into a type using 'forceTyCo'.
forceTy
  :: HasCallStack
  => () !> es
  => Arg es
  -> Result es Type
forceTy = forceTyCo >=> either pure (const $ throw ())

-- | Force an expression into a coercion using 'forceTyCo'.
forceCo
  :: HasCallStack
  => () !> es
  => Arg es
  -> Result es Coercion
forceCo = forceTyCo >=> either (const $ throw ()) pure

-- | Convert an expression of type Bool to a symbolic boolean.
exprToBool
  :: HasCallStack
  => () !> es
  => Expr es
  -> Eval es SymBool
exprToBool = \case
  Lit (DataCon tag tc) | tc == boolTyCon -> do
    -- DataCon are checked at creation for correctness. Hence, we can simply
    -- cast the bit value.
    pure $ bitCast (sizedBVResizeZ @_ @_ @1 tag)

  _ -> throwE ()

-- | Equivalence between literals.
--
-- NOTE: This only handles cases that may occur in a case expression.
eqLit
  :: HasCallStack
  => () !> es
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

-- TODO: This function deserves some clean-up! My syntax highlighter is even
-- breaking on it...
exprType
  :: HasCallStack
  => () !> es
  => Expr fs
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
        let subst = GHC.extendTCvSubst (GHC.mkEmptySubst scope) var aty
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
anyDataCon tag tc = concreteDataCon tag tc <|> if
  -- Enumeration TyCon all have the same type, so we just select the first
  -- one. We special case this as the tag of an enumeration may be an
  -- arbitrary arithmetic expression from which we cannot extract a concrete
  -- DataCon.
  | isEnumerationTyCon tc
  , dc : _ <- tyConDataCons tc -> pure dc
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
  :: Expr es
  -> (Expr es, [Arg es])
collectArgs = second (fmap unthunk) . collectThunks

-- | Collect the thunks of an application.
collectThunks
  :: Expr es
  -> (Expr es, [Thunk es])
collectThunks = go []
  where
    go args = \case
      App fun arg -> go (arg: args) fun
      expr -> (expr, args)

-- | Transform thunks into arguments.
--
-- Really, args are just always thunks. This will put forced values into thunks.
unthunk
  :: Thunk es
  -> Arg es
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
  :: HasCallStack
  => () !> es
  => Expr es
  -> Eval es (Either Coercion Literal, [Arg es])
collectScrut = \case
  -- On a cast, we may attempt to push a TyConAppCo into the arguments of
  -- a DataCon literal.
  Cast body co -> do
    -- Perform the operation for every body in the cast.
    body' <- liftUnion body

    -- Collect the spine and arguments.
    let (spine, args) = collectThunks body'

    -- Only a DataCon spine may have its arguments pushed.
    (SomeNat @n _, dc) <- case spine of
      Lit (DataCon @n tag tc)
        | Just dc <- anyDataCon tag tc -> pure (SomeNat @n Proxy, dc)
      _ -> throwE ()

    -- Push the coercion into the arguments.
    (_univ, args') <- liftR $ pushCoDataCon dc args co
    pure (Right $ mkDataCon @n dc, unthunk <$> args')

  -- If not a cast, we attempt to get the literal at the spine and return the
  -- arguments excluding the universal type arguments.
  expr -> do
    -- Gather the spine and its arguments.
    let (spine, args) = collectArgs expr

    -- Gathers the number of universal arguments of a literal.
    let nUnivLit = \case
          DataCon _ tc -> tyConArity tc
          -- TODO: Use or pattern once we bump the GHC version.
          Int {} -> 0
          Word {} -> 0
          Integer {} -> 0

    -- Gather the spine as either a literal or coercion and the number of
    -- universal arguments.
    (spine', nUniv) <- case spine of
      Lit lit -> pure (Right lit, nUnivLit lit)
      Coercion co -> pure (Left co, 0)
      _ -> throwE ()

    -- Drop the universal arguments and return.
    let args' = drop nUniv args
    pure (spine', args')

-- | Push a TyConAppCo into the arguments of a DataCon.
pushCoDataCon
  :: HasCallStack
  => () !> es
  => DataCon
  -> [Thunk es]
  -> Coercion
  -> Result es ([Type], [Thunk es])
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

-- | Throw an error within the 'Eval' monadic context.
throwE
  :: HasCallStack
  => e !> es
  => e
  -> Eval es a
throwE = Eval . withFrozenCallStack throw

-- | Throw the given error on 'Nothing' within the 'Eval' monadic context.
failWithE
  :: HasCallStack
  => e !> es
  => e
  -> Maybe a
  -> Eval es a
failWithE = liftR .: withFrozenCallStack failWith

-- | Lift a result into the evaluation context.
liftR :: Result es a -> Eval es a
liftR = Eval . fmap pure
