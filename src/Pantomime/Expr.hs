{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module Pantomime.Expr
  ( Eval
  , EvalError (..)
  , Variant (..)
  , Expr (..)
  , Arg
  , Literal (..)
  , Type
  , Coercion

  , pprExpr
  , pprArg

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

  , eqType
  , eqLit
  , exprType
  , litType
  , concreteDataCon
  , collectArgs
  , collectScrut

  , throwError'
  , whyFail'
  , dbgE
  ) where

import GHC.Plugins qualified as GHC
import GHC.Core.Type qualified as GHC
import GHC.Core.TyCo.Compare (eqType)
import GHC.Core.Ppr (pprOptCo)
import GHC.Core.TyCo.Rep (scaledThing)
import GHC.Core.Opt.Arity
  ( pushCoTyArg
  , pushCoValArg
  )
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
  )

import GHC.TypeNats
  ( KnownNat
  )
import GHC.Generics
  ( Generic
  , Generic1
  )
import GHC.Stack
  ( CallStack
  , callStack
  , prettyCallStack
  )

import Grisette.Unified (EvalModeTag (..))
import Grisette
  ( Union
  , SymBool
  , SymInteger
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
  , liftUnion
  , pattern Single
  , pattern If
  )

import Pantomime.Orphan.GHC ()
import Pantomime.Grisette.SomeBV (SomeBV (..))
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

import Data.List ((!?))
import Data.Traversable (for)
import Data.Typeable
  ( type (:~:) (..)
  , eqT
  )

import Control.Arrow (Arrow(..))
import Control.Applicative (Alternative(..))
import Control.Monad.Except
  ( MonadError (..)
  , ExceptT (..)
  , runExceptT
  )
import Control.Monad
  ( foldM
  , unless
  )

import Debug.Trace qualified as Debug

dbgE :: GHC.Outputable o => o -> Eval ()
dbgE m = Debug.trace (GHC.showSDocUnsafe $ GHC.ppr m) $ pure ()

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
  -- TODO: Should this not contain an Eval Expr? In any case, we haven't really
  -- implemented errors yet, so we should just look into this still.
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
  -- TODO: Shouldn't Forced just be an (Either Type Coercion)? We really don't
  -- want to force anything else no?
  Forced :: Expr -> Thunk
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
  (tc, targs) <- whyFail' () $ splitTyConApp_maybe ty
  unless (isEnumerationTyCon tc) do
    throwError' ()

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
    (ty', rco) <- whyFail' () $ pushCoTyArg co ty

    -- Return the type argument and result coercion.
    pure (pure $ mkType ty', rco)

  | otherwise -> do
    -- Attempt to split the coercion into an argument and result coercion.
    (aco, rco) <- whyFail' () $ pushCoValArg co

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
  :: HasCallStack
  => MonadError (EvalError ()) m
  => Expr
  -> m Type
exprType = \case
  Lit lit -> litType lit
  Type _ -> throwError' ()
  Coercion co -> pure $ coercionType co
  Lam ty _ -> pure ty
  App fun arg -> do
    -- TODO: Recursive call grows callstack, fix this!
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
    -- Gather a literal and it's arguments if possible.
    (lit, args) <- case collectArgs expr of
      (Lit lit, args) -> pure (lit, args)
      _ -> throwError' ()

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
      -- TODO: Do we need to wrap Coercions with mkCoercionTy?
      Forced (Type ty) -> pure ty
      _ -> throwError' ()
    valArgs' <- for valArgs \case
      Thunked value -> pure value
      Forced _ -> throwError' ()
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
  let exArgs = Forced . Type <$> exTys'

  pure (univArgsR, exArgs ++ valArgs')

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
