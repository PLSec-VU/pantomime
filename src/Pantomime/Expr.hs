{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module Pantomime.Expr4
  ( Eval
  , EvalError (..)
  , Expr (..)
  , Literal (..)

  , pprExpr
  , pprArg

  , mkLit
  , mkDataCon
  , mkIntN
  , mkWordN
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

  , eqLit
  , exprType
  , litType
  , collectArgs
  , collectScrut

  , freshExpr
  , saturate

  , throwError'

  , Subst
  , emptySubst
  , extendSubst
  , extendSubstMany
  , lookupId
  , substTy
  , substCo
  ) where

import Prelude hiding (Semigroup (..))

import GHC.Plugins qualified as GHC
import GHC.Core.Type qualified as GHC
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.Ppr (pprOptCo)
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Core.Reduction (Reduction(..))
import GHC.Core.Opt.Arity
  ( pushCoTyArg
  , pushCoValArg
  )
import GHC.Builtin.Types.Prim
import GHC.Core.FamInstEnv
  ( FamInstEnvs
  , topNormaliseType_maybe
  )
import GHC.Types.Unique
  ( Uniquable(..)
  , getKey
  )
import GHC.Utils.Outputable
  ( IsLine (..)
  , SDoc
  , ($+$)
  , parens
  , hang
  , nest
  , showSDocUnsafe
  )
import GHC.Plugins
  ( Type
  , Coercion
  , CoercionR
  , MCoercionR
  , MCoercion (..)
  , Role (..)
  , Var
  , Name
  , HasOccName (..)
  , TyCon
  , DataCon
  , HasCallStack
  , Outputable (..)
  , CvSubstEnv
  , TvSubstEnv
  , IdEnv
  , InScopeSet
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
  , mkEmptySubst
  , extendTCvSubst
  , emptyInScopeSet
  , emptyVarEnv
  , isTyVar
  , isCoVar
  , extendVarEnv
  , lookupVarEnv
  , mkSymCo
  , tcSplitTyConApp_maybe
  , isDataTyCon
  , isUnboxedTupleTyCon
  , isUnboxedSumTyCon
  , tyConDataCons_maybe
  , dataConInstArgTys
  , splitForAllTyVars
  , mkTyVarTy
  , splitFunTys, splitTyConApp_maybe, dataConExTyCoVars, splitAtList, dropList, dataConUnivTyVars, decomposeCo, tyConArity, tyConRolesRepresentational, liftCoSubstWithEx, dataConRepArgTys
  )

import GHC.TypeNats (KnownNat, SomeNat (..))
import GHC.Generics (Generic, Generic1)
import GHC.Stack (CallStack, callStack, prettyCallStack)

import Grisette.Unified (EvalModeTag (..))
import Grisette
  ( Union
  , Symbol
  , Solvable (..)
  , ConRep (..)
  , SExpr (..)
  , SymEq (..)
  , ToSym (..)
  , ToCon (..)
  , TryMerge (..)
  , Mergeable (..)
  , Mergeable1 (..)
  , SimpleMergeable (..)
  , SimpleMergeable1 (..)
  , SymBranching (..)
  , MergingStrategy (..)
  , Default (..)
  , Default1 (..)
  , wrapStrategy
  , product2Strategy
  , liftUnion
  , simple
  , withMetadata
  , pattern Single
  , pattern If, SymBool
  )

import Pantomime.Orphan.GHC ()
import Pantomime.Grisette.BitVector
  ( IntN
  , WordN
  )
import Pantomime.Util
  ( foldM'
  , freshIds
  )

import Data.Either (isLeft)
import Data.String (IsString(..))
import Data.List ((!?))
import Data.Functor ((<&>))
import Data.Typeable
  ( type (:~:) (..)
  , Proxy (..)
  , eqT
  )

import Control.Monad.Except
  ( MonadError (..)
  , ExceptT (..)
  , runExceptT
  )
import Control.Monad
  ( foldM
  , unless
  , join
  )
import Data.Traversable (for)
import Control.Arrow (Arrow(..))
import Clash.Explicit.Prelude (Alternative(..))

-- TODO: I want to add plucky error values to Eval. Note that I also want to
-- get rid of the MonadError there.
--
-- TODO: I think the Mergeable instance should have a NoStrategy on the
-- evaluation errors of Eval. That is, I really don't want to merge actual
-- errors. Note, it is completely fine to merge the Variant. I guess the best
-- way to solve this would just be to make a wrapper type for the error that
-- has NoStrategy. Hmm. I guess perhaps we could merge btw. As in, we could have
-- the same error trigger multiple times as an expression may be duplicated. We
-- can see if we can merge CallStack such that we only merge if an error has the
-- same origin? Of course, this could cause false merging if we accidentially
-- cut the CallStack short. Still, I think it has benefits as well!
newtype Eval a where
  Eval :: ExceptT (EvalError ()) (ExceptT Variant Union) a -> Eval a
  deriving Functor
  deriving Applicative
  deriving Monad
  deriving (MonadError (EvalError ()))
  deriving Generic
  deriving Mergeable via Default (Eval a)
  deriving SimpleMergeable via Default (Eval a)
  deriving Generic1
  deriving Mergeable1 via Default1 Eval
  deriving SimpleMergeable1 via Default1 Eval

data EvalError a where
  EvalError :: CallStack -> a -> EvalError a

-- TODO: I'm not sure if I like this name. Perhaps we can think about what other
-- options these have. Unlike the other error types, these ones don't need a
-- stack trace, as they're actually just valid values. In fact, I **really**
-- want these to merge! Perhaps something like NominalExcept/Error?
data Variant where
  UB :: Variant
  Unreachable :: Variant
  Raise :: Expr -> Variant
  deriving Generic
  deriving Mergeable via Default Variant

data Expr where
  Lit
    :: Literal
    -> Expr
  Type
    :: Type
    -> Expr
  Coercion
    :: CoercionR
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
  Forced :: Expr -> Thunk
  deriving Generic
  deriving Mergeable via Default Thunk

data Literal where
  -- TODO: I think it makes sense to place the universal type arguments of a
  -- DataCon inside of the literal. The reason I say this is that a tagToEnum#
  -- call actually expects the type to coerce to. If this were to represent this
  -- call (i.e by storing a enumeration TyCon), then we cannot really print it
  -- as a call to tagToEnum# if it doesn't have its type arguments.
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

-- | Partial merging strategy.
--
-- Sometimes we do not want to (or cannot) merge values. This function allows
-- one to encode which states are mergeable. The remaining patterns will receive
-- 'NoStrategy' as merging strategy.
partialStrategy
  :: (r -> a)
  -> (a -> Maybe r)
  -> MergingStrategy r
  -> MergingStrategy a
partialStrategy wrap unwrap strategy = do
  wrapStrategy
    -- Use inner merging strategy only if possible.
    (ifStrategy
      isLeft
      NoStrategy
      (wrapStrategy
        strategy
        Right
        \case Right value -> value; _ -> impossible))

    -- Wrap unmergeable value in Left and mergeable ones in Right.
    (either id wrap)

    -- Unwrap from original value or merged one.
    (\value -> maybe (Left value) Right $ unwrap value)

-- | If strategy.
--
-- Depending on a predicate on a mergeable value, use either the first or the
-- second strategy.
ifStrategy
  :: (a -> Bool)
  -> MergingStrategy a
  -> MergingStrategy a
  -> MergingStrategy a
ifStrategy f true false = SortedStrategy f \case
  True -> true
  False -> false

-- | Product strategy specialised to a tuple.
tupleStrategy
  :: MergingStrategy a
  -> MergingStrategy b
  -> MergingStrategy (a, b)
tupleStrategy = product2Strategy (,) id

-- | Marker to use for unreachable branches in merging strategies.
impossible :: HasCallStack => a
impossible = error "BUG: sorted strategy should ensure this path is unreachable"

instance Mergeable Literal where
  rootStrategy = SortedStrategy
    (\case
      DataCon _ _ -> 0 :: Int
      Int _ _ -> 1
      Word _ _ -> 2)
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

      _ -> impossible

instance TryMerge Eval where
  tryMergeWithStrategy strategy (Eval m) = do
    Eval $ tryMergeWithStrategy strategy m

instance SymBranching Eval where
  mrgIfWithStrategy strategy scrut (Eval true) (Eval false) = do
    Eval $ mrgIfWithStrategy strategy scrut true false

  mrgIfPropagatedStrategy scrut (Eval true) (Eval false) = do
    Eval $ mrgIfPropagatedStrategy scrut true false

instance Mergeable (EvalError a) where
  rootStrategy = NoStrategy

pprExpr
  :: (SDoc -> SDoc)
  -> Expr
  -> SDoc
pprExpr addParens = \case
  Lit lit -> ppr lit
  Type ty -> "@" <> ppr ty
  Coercion co -> "@~" <> ppr co
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
pprArg addParens (Eval arg) = do
  let f p = \case
        Left UB -> "UB"
        Left Unreachable -> "Unreachable"
        Left (Raise expr) -> "raise#" <+> pprExpr p expr
        Right (Right expr) -> pprExpr p expr
        Right (Left (EvalError trace ())) -> "UNKNOWN ERROR :(" $+$ text (prettyCallStack trace)
  pprUnion addParens f $ runExceptT (runExceptT arg)

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
      | isEnumerationTyCon tc -> "tagToEnum#" <+> "@" <> ppr tc <+> ppr (SomeBV tag)
      | otherwise -> "INVALID DATACON"
    Int value ty -> ppr (SomeBV value) <+> "::" <+> ppr ty
    Word value ty -> ppr (SomeBV value) <+> "::" <+> ppr ty

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
  :: Expr
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
    ty <- exprType fun
    if
      | isFunTy ty -> pure $ App fun (Thunked arg)
      | isForAllTy ty -> do
        forced <- arg
        pure $ App fun (Forced forced)
      | otherwise -> throwError' ()

pushCoArg
  :: HasCallStack
  => CoercionR
  -> Arg
  -> Eval (Arg, MCoercionR)
pushCoArg co arg = if
  | tyL <- coercionLKind co
  , isForAllTy_ty tyL -> do

    -- The argument needs to be a type. As such, we can force it.
    ty <- arg >>= \case
      Type ty -> pure ty
      _ -> throwError' ()

    -- Attempt to push the coercion into the type argument.
    (ty', rco) <- case pushCoTyArg co ty of
      Just result -> pure result
      _ -> throwError' ()

    pure (pure $ mkType ty', rco)

  | otherwise -> do
    (aco, rco) <- case pushCoValArg co of
      Just result -> pure result
      _ -> throwError' ()
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
    throwError' ()

  -- Ensure the cast can be applied to the expression.
  ty <- exprType expr
  unless (eqType ty $ coercionLKind co) do
    -- FIXME: Make this a proper error.
    throwError' ()

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

    -- TODO: What about TyConAppCo? Shouldn't we reduce this as well? Or perhaps
    -- that would be best left to when we try to pattern match? Idk...

    _ -> pure $ Cast (pure expr) co

mkVariant
  :: Variant
  -> Eval a
mkVariant = Eval . ExceptT . throwError

mkUnreachable :: Eval a
mkUnreachable = mkVariant Unreachable

mkUB :: Eval a
mkUB = mkVariant UB

mkRaise :: Expr -> Eval a
mkRaise = mkVariant . Raise

eqLit
  :: MonadError (EvalError ()) m
  => Literal
  -> Literal
  -> m SymBool
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
  _ _ -> throwError' ()

-- TODO: I split away the Eval from this as I'm only using the error. I don't
-- like the monad error constraint too much though, so I want to find a better
-- solution sometime.
exprType
  :: MonadError (EvalError ()) m
  => Expr
  -> m Type
exprType = \case
  Lit lit -> litType lit
  Type _ -> throwError' ()
  Coercion co -> pure $ coercionType co
  Lam ty _ -> pure ty
  App fun arg -> do
    fty <- exprType fun
    if
      | Just (var, rty) <- splitForAllTyCoVar_maybe fty -> do
        aty <- case arg of
          Forced (Coercion co) -> pure $ mkCoercionTy co
          Forced (Type ty) -> pure ty
          _ -> throwError' ()
        let scope = mkInScopeSet $ tyCoVarsOfTypes [aty, rty]
        let subst = extendTCvSubst (mkEmptySubst scope) var aty
        pure $ GHC.substTy subst rty

      | Just (_, _, _, rty) <- splitFunTy_maybe fty -> pure rty

      | otherwise -> throwError' ()
  Cast _ co -> pure $ coercionRKind co

litType
  :: MonadError (EvalError ()) m
  => Literal
  -> m Type
litType = \case
  DataCon tag tc -> do
    dc <- whyFail' () $ anyDataCon tag tc
    pure $ dataConRepType dc

  Int _ ty -> pure ty
  Word _ ty -> pure ty

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

collectArgs
  :: Expr
  -> (Expr, [Arg])
collectArgs = second (fmap unthunk) . collectThunks

collectThunks
  :: Expr
  -> (Expr, [Thunk])
collectThunks = go []
  where
    go args = \case
      App fun arg -> go (arg: args) fun
      expr -> (expr, args)

unthunk
  :: Thunk
  -> Arg
unthunk = \case
  Thunked value -> value
  Forced value -> pure value

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
      _ -> throwError' ()

    -- Only a DataCon may have its arguments pushed.
    dc <- case lit of
      DataCon tag tc | Just dc <- anyDataCon tag tc -> pure dc
      _ -> throwError' ()

    -- Push the coercion into the arguments.
    (_univ, args') <- pushCoDataCon dc args co
    pure (lit, unthunk <$> args')

  -- If not a cast, we attempt to get the literal at the spine and return the
  -- arguments excluding the universal type arguments.
  expr -> do
    (lit, args) <- case collectArgs expr of
      (Lit lit, args) -> pure (lit, args)
      _ -> throwError' ()

    let univ = case lit of
          DataCon _ tc -> tyConArity tc
          Int {} -> 0
          Word {} -> 0

    pure (lit, drop univ args)

pushCoDataCon
  :: MonadError (EvalError ()) m
  => DataCon
  -> [Thunk]
  -> Coercion
  -> m ([Type], [Thunk])
pushCoDataCon dc args co = do
  -- Check whether the outer type is a TyConAppCo.
  let tyR = coercionRKind co
  (tcR, univArgsR) <- whyFail' () $ splitTyConApp_maybe tyR
  unless (tcR == dataConTyCon dc) do
    throwError' ()

  -- Gather information on type variables of the DataCon.
  let dcUnivVars = dataConUnivTyVars dc
  let dcExVars = dataConExTyCoVars dc

  -- Get the existential and value arguments.
  (exTys, valArgs) <- do
    let (exArgs, valArgs) = splitAtList dcExVars $ dropList dcUnivVars args
    exTys <- for exArgs \case
      Forced (Type ty) -> pure ty
      _ -> throwError' ()
    valArgs' <- for valArgs \case
      Thunked value -> pure value
      Forced _ -> throwError' ()
    pure (exTys, valArgs')

  -- Get coercions for the universal type variables.
  let univCo = decomposeCo (tyConArity tcR) co $ tyConRolesRepresentational tcR

  -- Create the new existential type arguments and the type substitution for
  -- the inner casts.
  let (psiSubst, exTys')
        = liftCoSubstWithEx Representational dcUnivVars univCo dcExVars exTys

  -- Cast all the value arguments using the substitution.
  let argTys = scaledThing <$> dataConRepArgTys dc
  let castArg arg ty = arg >>= flip mkCast (psiSubst ty)
  let valArgs' = Thunked <$> zipWith castArg valArgs argTys

  -- Wrap the existential type arguments back into thunks.
  let exArgs = Forced . Type <$> exTys'

  pure (univArgsR, exArgs ++ valArgs')

data Variable where
  Variable ::
    { varName :: Name
    -- ^ Root name.
    , varAccessor :: [Accessor]
    -- ^ Accessor path, note that the first entry is accessed last.
    , varType :: Type
    -- ^ Type of this variable.
    , varArgs :: [Arg]
    -- ^ Arguments which the variable depends on.
    } -> Variable

data Accessor where
  Accessor
    :: DataCon
    -- ^ The data constructor to access.
    -> Int
    -- ^ The field number to access.
    -> Accessor

data FieldOrTag where
  Field :: FieldOrTag
  Tag :: FieldOrTag

varToSymbol
  :: Variable
  -> FieldOrTag
  -> Symbol
varToSymbol var dst = do
  -- TODO: Clean this function up! It's super ugly!
  let name = fromString . showSDocUnsafe . ppr . occName . varName $ var
  let unique = NumberAtom . toInteger . getKey . getUnique . varName $ var
  let dst' = case dst of
        Field -> Atom "field"
        Tag -> Atom "tag"
  let accessors = flip fmap (varAccessor var) \(Accessor dc idx) -> do
        List $ fmap (NumberAtom . toInteger) [dataConTagZ dc, idx]
  let meta = List $ unique : dst' : accessors
  let ident = withMetadata name meta
  simple ident

symbolicVar
  :: Solvable (ConType s) s
  => Variable
  -> FieldOrTag
  -> s
symbolicVar var dst = case varArgs var of
  [] -> sym $ varToSymbol var dst
  -- FIXME: We should be able to generate symbolic functions that take a number
  -- of arguments.
  -- TODO: What if arguments differ? Will this generate a different function
  -- everytime? I'm not sure how this would work, but I guess as long as the
  -- method of creation is the same it should work.
  _ -> error "Not implemented yet :("

freshExpr
  :: HasCallStack
  => FamInstEnvs
  -> Var
  -> Arg
freshExpr famInst root = go Variable
  { varName = GHC.varName root
  , varAccessor = []
  , varType = GHC.varType root
  , varArgs = []
  }
  where
    go var = do
      -- TODO: I don't like the nesting this gives. Maybe we should move these
      -- inwards somehow. The ty can actually be replaced by pattern match on
      -- the var btw.
      let ty = varType var
      let symbolic :: Solvable (ConType s) s => s
          symbolic = symbolicVar var Field
      if
        -- Primitives:
        --------------
        -- | ty `eqType` intPrimTy -> pure $ mkIntN @n symbolic
        | ty `eqType` int8PrimTy -> pure $ mkLit (mkIntN @8 symbolic ty)
        | ty `eqType` int16PrimTy -> pure $ mkLit (mkIntN @16 symbolic ty)
        | ty `eqType` int32PrimTy -> pure $ mkLit (mkIntN @32 symbolic ty)
        | ty `eqType` int64PrimTy -> pure $ mkLit (mkIntN @64 symbolic ty)
        -- | ty `eqType` wordPrimTy -> pure $ mkWordN @n symbolic
        | ty `eqType` word8PrimTy -> pure $ mkLit (mkWordN @8 symbolic ty)
        | ty `eqType` word16PrimTy -> pure $ mkLit (mkWordN @16 symbolic ty)
        | ty `eqType` word32PrimTy -> pure $ mkLit (mkWordN @32 symbolic ty)
        | ty `eqType` word64PrimTy -> pure $ mkLit (mkWordN @64 symbolic ty)
        -- | ty `eqType` floatPrimTy -> undefined
        -- | ty `eqType` doublePrimTy -> undefined

        -- Type Family Reduction:
        -------------------------
        | Just reduction <- topNormaliseType_maybe famInst (varType var) -> do
          let co = mkSymCo $ reductionCoercion reduction
          let ty' = reductionReducedType reduction
          let var' = var { varType = ty' }
          inner <- go var'
          mkCast inner co

        -- Algebraic Data Types:
        ------------------------
        | Just (tyCon, tyArgs) <- tcSplitTyConApp_maybe ty
        , or
          [ isDataTyCon tyCon
          , isUnboxedTupleTyCon tyCon
          , isUnboxedSumTyCon tyCon
          ]
        , Just dataCons <- tyConDataCons_maybe tyCon -> do
          -- FIXME: This should get the proper platform size.
          let tag = symbolicVar @(IntN S 64) var Tag

          -- TODO: This creates a long list of negated equalities for the
          -- unreachable case: tag != 0 && tag != 1 ... tag != n
          -- Instead, I wonder if it is not better to generate tag < n?
          --
          -- I guess another way to solve this would be order the Unreachable
          -- state at the end? That way, we just get a natural chain of if-then
          -- else until unreachable. I feel like this might hurt other merges
          -- though...
          --
          -- Another thing to look out for is that for enumeration TyCon, we
          -- generate.
          -- ite
          --   (tag == 0)
          --   0
          --   (ite
          --     (tag == 1)
          --     1
          --     ...)
          --
          -- But really, we should just generate the equivalent expression:
          -- tag
          --
          -- Note I skipped writing the Unreachable case in both examples.
          join $ foldM' mkUnreachable dataCons \acc dc -> do
            let scrut = tag .== fromIntegral (dataConTagZ dc)

            let fieldTys = scaledThing <$> dataConInstArgTys dc tyArgs
            let args = zip [0..] fieldTys <&> \(idx, ty') -> do
                  go var
                    { varType = ty'
                    , varAccessor = Accessor dc idx : varAccessor var
                    }

            -- FIXME: This should get the proper platform size.
            let dc' = mkLit $ mkDataCon @64 dc
            let tyArgs' = pure . mkType <$> tyArgs
            let expr = mkApps dc' (tyArgs'  ++ args)

            pure $ mrgIte scrut expr acc

        | otherwise -> throwError' ()

saturate
  :: FamInstEnvs
  -> Expr
  -> Eval (Expr, [(Var, Arg)])
saturate famInst expr = do
  -- TODO: I don't want to generate new arguments for each inner expression. I
  -- just want arguments once. If I can do exprType for the whole thing, then
  -- perhaps I can change the type of this to (Eval Expr, [(Var, Arg)]).
  ty <- exprType expr
  let (tvs, bty) = splitForAllTyVars ty
  let tyArgs = pure . mkType . mkTyVarTy <$> tvs
  let (atys, _) = splitFunTys bty
  let (avars, _) = freshIds (zip (repeat "arg") atys) emptyInScopeSet
  let exprArgs = freshExpr famInst <$> avars
  -- FIXME: Using these tvs is not really great: We should really generate fresh
  -- ones given the current in-scope set.
  let vars = tvs ++ avars
  let args = tyArgs ++ exprArgs
  result <- mkApps expr args
  pure (result, zip vars args)

-- TODO: This is horrible. It's better than not having a callstack, but we
-- should really improve the error handling. Also, this should really not add
-- it's own callstack to the throw no?
throwError'
  :: HasCallStack
  => MonadError (EvalError a) m
  => a
  -> m b
throwError' = throwError . EvalError callStack

-- TODO: The callstack should probably be frozen before calling the throw.
whyFail'
  :: HasCallStack
  => MonadError (EvalError a) m
  => a
  -> Maybe b
  -> m b
whyFail' err = maybe (throwError' err) pure

data Subst where
  Subst ::
    { scSubst :: InScopeSet
    , idSubst :: IdEnv (Eval Expr)
    , tvSubst :: TvSubstEnv
    , cvSubst :: CvSubstEnv
    } -> Subst

emptySubst :: Subst
emptySubst = Subst
  { scSubst = emptyInScopeSet
  , idSubst = emptyVarEnv
  , tvSubst = emptyVarEnv
  , cvSubst = emptyVarEnv
  }

extendSubst
  :: Subst
  -> Var
  -> Arg
  -> Eval Subst
extendSubst subst var arg = if
  | isTyVar var -> do
    -- FIXME: We currently create a new substitution for every type argument
    -- that exists. This might introduce a huge amount of code paths. Consider
    -- for example a data type with 3 existentials, each with two options.
    -- If we case split for every one, we get 8 executions. Likely, only 2 of
    -- those were actually possible in the first place.
    --
    -- The alternatives would be:
    -- 1. Let the tvSubst (and cvSubst) be a Union, so they themselves may
    -- return different values once they're required.
    -- 2. If we really won't ever even rely on this behaviour of having multiple
    -- types in one Union, then we should just check here whether we have
    -- strictly one value! The monad should also just be an error one instead of
    -- Eval in this case btw. The current implementation is actually heavily
    -- leaning in this direction!

    -- Ensure that the variables are only types. Note that we force the
    -- evaluation here as type reduction should always terminate.
    ty <- arg >>= \case
      Type ty -> pure ty
      _ -> throwError' ()

    -- Extend the type variable substitution.
    let tvSubst' = extendVarEnv (tvSubst subst) var ty
    pure subst { tvSubst = tvSubst' }

  | isCoVar var -> do
    -- Ensure that the variables are only types. Note that we force the
    -- evaluation here as type reduction should always terminate.
    co <- arg >>= \case
      Coercion co -> pure co
      _ -> throwError' ()

    -- Extend the coercion variable substitution.
    let cvSubst' = extendVarEnv (cvSubst subst) var co
    pure subst { cvSubst = cvSubst' }

  | otherwise -> do
    -- Extend the identifier substitution.
    let idSubst' = extendVarEnv (idSubst subst) var arg
    pure subst { idSubst = idSubst' } 

extendSubstMany
  :: Foldable f
  => Subst
  -> f (Var, Arg)
  -> Eval Subst
extendSubstMany = foldM $ uncurry . extendSubst

lookupId
  :: HasCallStack
  => Subst
  -> Var
  -> Eval Expr
lookupId subst = join . whyFail' () . lookupVarEnv (idSubst subst)

substTy
  :: Subst
  -> Type
  -> Type
substTy subst ty = do
  let subst' = tyCoSubst subst
  GHC.substTy subst' ty

substCo
  :: Subst
  -> Coercion
  -> Coercion
substCo subst ty = do
  let subst' = tyCoSubst subst
  GHC.substCo subst' ty

tyCoSubst :: Subst -> GHC.Subst
tyCoSubst Subst { .. } = GHC.Subst scSubst emptyVarEnv tvSubst cvSubst

-- TODO: This thing should get its own module!
data SomeBV bv where
  SomeBV :: KnownNat n => bv n -> SomeBV bv

instance (forall n. KnownNat n => Show (bv n)) => Show (SomeBV bv) where
  show (SomeBV value) = show value

-- FIXME: This should really use the inner Outputable instance.
instance (forall n. KnownNat n => Show (bv n)) => Outputable (SomeBV bv) where
  ppr = text . show

instance (forall n. KnownNat n => Mergeable (bv n)) => Mergeable (SomeBV bv) where
  rootStrategy = SortedStrategy
    (\(SomeBV @n _) -> SomeNat @n Proxy)
    (\(SomeNat @n _) -> wrapStrategy @(bv n)
      rootStrategy
      SomeBV
      \case SomeBV @m bv | Just Refl <- eqT @n @m -> bv ; _ -> impossible)

instance (forall n. KnownNat n => ToSym (bva n) (bvb n)) => ToSym (SomeBV bva) (SomeBV bvb) where
  toSym (SomeBV @n bv) = SomeBV @n $ toSym bv

instance (forall n. KnownNat n => ToCon (bva n) (bvb n)) => ToCon (SomeBV bva) (SomeBV bvb) where
  toCon (SomeBV @n bv) = SomeBV @n <$> toCon bv
