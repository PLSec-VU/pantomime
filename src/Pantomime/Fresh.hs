{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Fresh
  ( FreshInstEnv (..)
  , freshExpr
  , freshArgs
  ) where

import GHC.Core.Reduction
  ( Reduction(..)
  , HetReduction (..)
  , mkHetReduction
  , mkReduction
  , homogeniseHetRedn
  )
import GHC.Core.TyCo.Rep (scaledThing, UnivCoProvenance (..))
import GHC.Builtin.Types.Prim
  ( intPrimTy
  , int8PrimTy
  , int16PrimTy
  , int32PrimTy
  , int64PrimTy
  , wordPrimTy
  , word8PrimTy
  , word16PrimTy
  , word32PrimTy
  , word64PrimTy
  )
import GHC.Core.FamInstEnv
  ( FamInstEnvs
  , topNormaliseType
  , topReduceTyFamApp_maybe
  )
import GHC.Types.Unique
  ( Uniquable(..)
  , getKey
  )
import GHC.Core.TyCon.Env (TyConEnv, lookupTyConEnv)
import GHC.Utils.Outputable
  ( Outputable (..)
  , showSDocUnsafe
  )
import GHC.Plugins qualified as GHC
import GHC.Plugins
  ( Var
  , TyCon
  , Name
  , HasOccName (..)
  , DataCon
  , HasCallStack
  , InScopeSet
  , Role (..)
  , MCoercion (..)
  , NormaliseStepResult (..)
  , dataConTagZ
  , mkSymCo
  , isDataTyCon
  , isUnboxedTupleTyCon
  , isUnboxedSumTyCon
  , tyConDataCons_maybe
  , dataConInstArgTys
  , splitForAllTyVars
  , splitFunTys
  , splitTyConApp_maybe
  , mkTyConTy
  , isNumLitTy
  , tyVarKind
  , mkUnivCo
  , mkAppCos
  , mkReflCo
  , coreFullView
  , topNormaliseTypeX
  , composeSteppers
  , mkTransCo
  , mkTransMCo
  , unwrapNewTypeStepper, coercionRKind
  )

import GHC.TypeLits (someNatVal)
import GHC.TypeNats (SomeNat (..))

import Grisette.Unified (EvalModeTag (..))
import Grisette
  ( Symbol
  , Solvable (..)
  , ConRep (..)
  , SExpr (..)
  , SymEq (..)
  , SimpleMergeable (..)
  , simple
  , withMetadata
  )

import Data.Functor ((<&>))
import Data.String (IsString(..))

import Pantomime.Grisette.BitVector (IntN)
import Pantomime.Expr
import Pantomime.Primitive.GHC qualified as Primitive
import Pantomime.Util (freshIds, freshTyVars, foldlBy)
import Pantomime.Result (type (!>))
import GHC.Core.TyCon.RecWalk (checkRecTc)

data FreshInstEnv where
  FreshInstEnv ::
    { fieFam :: FamInstEnvs
    , fieUser :: TyConEnv TyCon
    , fiePrim :: Primitive.Types
    } -> FreshInstEnv

-- | Adaptation of GHC's 'topNormaliseType_maybe'.
--
-- Whilst most of the function body remains the same, the key difference is on
-- the reduction of newtypes. Specifically, we have a number of types that have
-- either a primitive or user-defined interpretation within the symbolic solver.
-- Normalising these newtypes normall would lose this mapping, thus producing
-- incoherent results with respect to the rest of the solver.
--
-- This modification will special case the primitive and user-mapped TyCon in
-- the reduction, to either skip or use the user-coercion respectively.
topNormaliseInterpType_maybe :: FreshInstEnv -> Type -> Maybe Reduction
topNormaliseInterpType_maybe FreshInstEnv { .. } ty = do
  -- TODO: If we want to make the primitive newtypes, we should add a stepper
  -- for them here!

  -- User interpretation stepper. This will create plugin coercions when it
  -- receives a TyCon that has a user-defined interpretation. Note that this
  -- should be ordered before the normal newtype stepper.
  let userInterpStepper recNts tc tys = either id id do
        let returnWith r = maybe (Left r) pure

        -- Check whether there exists a user-mapping.
        tc' <- returnWith NS_Done $ lookupTyConEnv fieUser tc

        -- Construct the coercion.
        let prov = PluginProv "pantomime user-defined"
        let tyL = mkTyConTy tc
        let tyR = mkTyConTy tc'
        let univ = mkUnivCo prov Representational tyL tyR
        let co = mkAppCos univ $ mkReflCo Nominal <$> tys

        -- Check the recursion counter before returning the step.
        let ty' = coercionRKind co
        recNts' <- returnWith NS_Abort $ checkRecTc recNts tc
        pure $ NS_Step recNts' ty' (co, MRefl)

  -- The newtype stepper, no changes w.r.t. original GHC function.
  let unwrapNewTypeStepper' recNts tc tys = do
        (, MRefl) <$> unwrapNewTypeStepper recNts tc tys

  -- The type-family stepper, no changes w.r.t. original GHC function.
  let tyFamStepper recNts tc tys = do
        let step (HetReduction (Reduction co rhs) resCo) = do
              NS_Step recNts rhs (co, resCo)

        maybe NS_Done step $ topReduceTyFamApp_maybe fieFam tc tys

  -- Normalise the type using a composition of the above defined steppers.
  let stepper = foldl' composeSteppers userInterpStepper
        [ unwrapNewTypeStepper'
        , tyFamStepper
        ]
  let combine (c1, mc1) (c2, mc2) = (c1 `mkTransCo` c2, mc1 `mkTransMCo` mc2)
  ((co, mkindCo), nty) <- topNormaliseTypeX stepper combine ty

  -- Construct the final reduction and homogenise it.
  let hredn = mkHetReduction (mkReduction co nty) mkindCo
  pure $ homogeniseHetRedn Representational hredn

data Variable es where
  Variable ::
    { varName :: Name
    -- ^ Root name.
    , varAccessor :: [Accessor]
    -- ^ Accessor path, note that the first entry is accessed last.
    , varType :: Type
    -- ^ Type of this variable.
    , varArgs :: [Arg es]
    -- ^ Arguments which the variable depends on.
    } -> Variable es

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
  :: Variable es
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
  => Variable es
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

-- TODO: This name isn't great. We really are making a symbolic expression here.
-- The freshness hinges on the freshness of the Var.
freshExpr
  :: HasCallStack
  => () !> es
  => FreshInstEnv
  -> Var
  -> EvalExpr es
freshExpr env@FreshInstEnv { .. } root = go Variable
  { varName = GHC.varName root
  , varAccessor = []
  , varType = GHC.varType root
  , varArgs = []
  }
  where
    go var = do
      -- TODO: I don't like the nesting this gives. Maybe we should move these
      -- inwards somehow.
      let ty = coreFullView $ varType var
      let symbolic :: Solvable (ConType s) s => s
          symbolic = symbolicVar var Field

      if
        -- Haskell Primitives:
        ----------------------
        -- FIXME: Generate proper platform size.
        | ty `eqType` intPrimTy -> pure $ mkLit (mkIntN @64 symbolic ty)
        | ty `eqType` int8PrimTy -> pure $ mkLit (mkIntN @8 symbolic ty)
        | ty `eqType` int16PrimTy -> pure $ mkLit (mkIntN @16 symbolic ty)
        | ty `eqType` int32PrimTy -> pure $ mkLit (mkIntN @32 symbolic ty)
        | ty `eqType` int64PrimTy -> pure $ mkLit (mkIntN @64 symbolic ty)
        -- FIXME: Generate proper platform size.
        | ty `eqType` wordPrimTy -> pure $ mkLit (mkWordN @64 symbolic ty)
        | ty `eqType` word8PrimTy -> pure $ mkLit (mkWordN @8 symbolic ty)
        | ty `eqType` word16PrimTy -> pure $ mkLit (mkWordN @16 symbolic ty)
        | ty `eqType` word32PrimTy -> pure $ mkLit (mkWordN @32 symbolic ty)
        | ty `eqType` word64PrimTy -> pure $ mkLit (mkWordN @64 symbolic ty)
        -- | ty `eqType` floatPrimTy -> undefined
        -- | ty `eqType` doublePrimTy -> undefined

        -- Pantomime Primitives:
        ------------------------
        -- Integer:
        | ty `eqType` mkTyConTy (Primitive.tcInteger fiePrim) -> do
          let value = mkInteger symbolic ty
          pure $ mkLit value

        -- IntN:
        | Just (tc, [arg]) <- splitTyConApp_maybe ty
        , tc == Primitive.tcIntN fiePrim
        -- TODO: Is this topNormaliseType sensible?
        , Just nat <- isNumLitTy $ topNormaliseType fieFam arg
        , Just (SomeNat @n _) <- someNatVal nat -> do
          -- FIXME: Should we place a Cast for the type families on the inner
          -- value. I think yes? We'll have to test it, but my guess is that any
          -- usage of will first have a cast for the type-level natural (only
          -- if it is symbolic btw).
          let value = mkIntN @n symbolic ty
          pure $ mkLit value

        -- TODO: Add remaining primitives

        -- Type Family, Newtype and User-Interpretations:
        -------------------------------------------------
        | Just reduction <- topNormaliseInterpType_maybe env ty -> do
          let co = mkSymCo $ reductionCoercion reduction
          let var' = var { varType = reductionReducedType reduction }
          inner <- go var'
          mkCast inner co

        -- Algebraic Data Types:
        ------------------------
        | Just (tyCon, tyArgs) <- splitTyConApp_maybe ty
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
          foldlBy mkUnreachable dataCons \acc dc -> do
            let scrut = tag .== fromIntegral (dataConTagZ dc)

            let fieldTys = scaledThing <$> dataConInstArgTys dc tyArgs
            let valArgs = zip [0..] fieldTys <&> \(idx, ty') -> do
                  go var
                    { varType = ty'
                    , varAccessor = Accessor dc idx : varAccessor var
                    }

            -- FIXME: This should get the proper platform size.
            let dc' = mkLit $ mkDataCon @64 dc
            let tyArgs' = pure . mkType <$> tyArgs
            let expr = mkApps dc' $ tyArgs' ++ valArgs

            mrgIte scrut expr acc

        -- TODO: Throw proper error!
        | otherwise -> do
          dbgE ["could not create fresh value for", ppr ty]
          throwE ()

freshArgs
  :: HasCallStack
  => () !> es
  => FreshInstEnv
  -> Type
  -> InScopeSet
  -> ([(Var, Arg es)], InScopeSet)
freshArgs freshEnv ty scope0 = do
  -- Gather the argument types.
  let (tyVars, funTy) = splitForAllTyVars ty
  let (argTys, _resTy) = splitFunTys funTy

  -- TODO: Isn't there some infinite sequence of names that could be used
  -- instead of this?
  -- Names for the arguments.
  let names = repeat @String "arg"

  -- Create fresh type arguments.
  let kinds = zip names $ fmap tyVarKind tyVars
  let (tyArgs, scope1) = freshTyVars kinds scope0

  -- Create fresh value arguments.
  let types = zip names argTys
  let (valArgs, scope2) = freshIds types scope1

  -- Collection of all arguments.
  let args = tyArgs <> valArgs

  -- Create symbolic instance of the arguments.
  let symbolic = freshExpr freshEnv <$> args

  -- Zip the binders together with their symbolic instance.
  let binders = zip args symbolic

  -- Return the binders and the new scope.
  (binders, scope2)
