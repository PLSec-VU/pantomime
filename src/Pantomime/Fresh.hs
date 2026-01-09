{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Fresh
  ( FreshInstEnv (..)
  , freshArgs
  ) where

import GHC.Core.Reduction (Reduction (..), mkReduction, homogeniseHetRedn)
import GHC.Core.TyCo.Rep (scaledThing, UnivCoProvenance (..))
import GHC.Core.FamInstEnv (topReduceTyFamApp_maybe)
import GHC.Types.Unique (Uniquable (..), getKey)
import GHC.Core.TyCon.Env (TyConEnv, lookupTyConEnv)
import GHC.Utils.Outputable (Outputable (..))
import GHC.Plugins qualified as GHC
import GHC.Plugins
  ( Var
  , TyCon
  , Name
  , DataCon
  , InScopeSet
  , Role (..)
  , dataConTagZ
  , isDataTyCon
  , isUnboxedTupleTyCon
  , isUnboxedSumTyCon
  , isEnumerationTyCon
  , tyConDataCons_maybe
  , dataConInstArgTys
  , splitForAllTyVars
  , splitFunTys
  , splitTyConApp_maybe
  , tyConFamilySize
  , tyVarKind
  , mkTyConTy
  , mkUnivCo
  , mkAppCos
  , mkReflCo
  , mkSymCo
  , mkSubCo
  , coreFullView
  , coercionRKind
  , instNewTyCon_maybe
  , getOccFS
  , bytesFS
  )

import Grisette
  ( Symbol
  , Solvable (..)
  , ConRep (..)
  , SExpr (..)
  , SymOrd (..)
  , SimpleMergeable (..)
  , simple
  , withMetadata
  , mrgIf
  )

import Data.Constraint (Dict (..))
import Data.Functor ((<&>))
import Data.Text.Encoding (decodeUtf8)

import Pantomime.Expr
import Pantomime.Literal
  ( BuiltInTyCon
  , SomeLiteralType (..)
  , HasDict (..)
  , reifyLitTy
  )
import Pantomime.Util (freshIds, freshTyVars, foldlBy, SymBitVec)

import Effectful
import Effectful.Error.Static
import Effectful.GHC.External
import Effectful.Context (Context, ContextMode (..))

data FreshInstEnv where
  FreshInstEnv ::
    { fieUser :: TyConEnv TyCon
    } -> FreshInstEnv

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

data VarType where
  Field :: VarType
  Tag :: VarType
  -- ^ Full tag, used for EnumCon.
  Select :: DataCon -> VarType
  -- ^ Select a specific DataCon.

-- TODO: This is not a great way to build identifiers for the tree. That is, the
-- identifiers grow with the size of the tree. We just want them to be a small
-- word ideally. Of course, this is better for id readability, but I think it
-- likely hurts performance. I'm not sure how Grisette implements this though.
-- I.e. whether they actually compare the full identifier. An alternative for
-- example would be to generate identifiers impurely with just a counter
-- (pure identifiers would have dependencies and thus would not work). For now,
-- this is better for debugging. I'll have to profile to see if this is actually
-- that bad. :)
varToSymbol
  :: Variable es
  -> VarType
  -> Symbol
varToSymbol var dst = do
  -- TODO: Clean this function up! It's super ugly!
  let name = decodeUtf8 . bytesFS . getOccFS . varName $ var
  let unique = NumberAtom . toInteger . getKey . getUnique . varName $ var
  let dcToSExpr = NumberAtom . toInteger . dataConTagZ
  let dst' = case dst of
        Field -> Atom "field"
        Tag -> Atom "tag"
        Select dc -> List [Atom "select", dcToSExpr dc]
  let accessors = flip fmap (varAccessor var) \(Accessor dc idx) -> do
        List [dcToSExpr dc, NumberAtom $ toInteger idx]
  let meta = List $ unique : dst' : accessors
  let ident = withMetadata name meta
  simple ident

symbolicVar
  :: Solvable (ConType s) s
  => Variable es
  -> VarType
  -> s
symbolicVar var dst = case varArgs var of
  [] -> sym $ varToSymbol var dst
  -- FIXME: We should be able to generate symbolic functions that take a number
  -- of arguments.
  -- TODO: What if arguments differ? Will this generate a different function
  -- everytime? I'm not sure how this would work, but I guess as long as the
  -- method of creation is the same it should work.
  _ -> error "Not implemented yet :("

-- TODO: I wonder if we could not push this creation to the front-end of
-- Pantomime. That is, we expose some functions to create fresh primitives.
-- Then we could probably use a Data instance to create remaining expression.
-- TODO: This name isn't great. We really are making a symbolic expression here.
-- The freshness hinges on the freshness of the Var.
freshExpr
  :: HasCallStack
  => Error () :> es
  => HasFamInstEnvs :> es
  => Context Reader BuiltInTyCon :> es
  => TyConEnv TyCon
  -> Var
  -> EvalExpr es
freshExpr axioms root = do
  -- TODO: Is it better to this lookup once? Whilst it is a reader-like effect,
  -- it is implemented through IO, so I'm a bit wary of running it in a hot loop
  -- like this one. The only way to know is just to profile I guess, but for now
  -- I'll put it outside.
  fam <- liftEff getFamInstEnvs
  -- TODO: Add note on callstack and recursion
  -- TODO: I don't like the nesting this gives. Maybe we should move these
  -- definitions inwards somehow. Perhaps just a standalone helper definition?
  -- This could also be useful for the callstack stuff :)
  let go var = do
        let ty = coreFullView $ varType var

        -- TODO: We can probably move the definition of this thing inwards once
        -- we remove the haskell primitives.
        let symbolic :: Solvable (ConType s) s => s
            symbolic = symbolicVar var Field

        let mkReductionCast reduction = do
              let co = mkSymCo $ reductionCoercion reduction
              let var' = var { varType = reductionReducedType reduction }
              inner <- go var'
              mkCast inner co

        -- TODO: Wouldn't it make more sense to have all the options be run by
        -- some sort of 'asum' like operation? Actually, NonDet from 'effectful'
        -- would be perfect! We should move the code that deals with
        -- reifyLitType adjecent to its call once we do this!
        result <- liftEff . runErrorNoCallStack @() $ reifyLitTy ty

        if
          -- Pantomime Primitive:
          -----------------------
          | Right (co, SomeLiteralType ty') <- result -> do
            Dict <- pure $ evidence ty'
            let value = Literal ty' symbolic
            mkCast (mkLit value) $ mkSubCo co

          -- User Interpretation:
          -----------------------
          | Just (tc, args) <- splitTyConApp_maybe ty
          , Just tc' <- lookupTyConEnv axioms tc -> do
            -- Construct the plugin coercion
            let prov = PluginProv "pantomime user-defined"
            let tyL = mkTyConTy tc
            let tyR = mkTyConTy tc'
            let univ = mkUnivCo prov Representational tyL tyR
            let co = mkAppCos univ $ mkReflCo Nominal <$> args

            -- Create the final expression.
            mkReductionCast $ mkReduction co (coercionRKind co)

          -- Type-Family:
          ---------------
          | Just (tc, args) <- splitTyConApp_maybe ty
          , Just hreduction <- topReduceTyFamApp_maybe fam tc args -> do
            mkReductionCast $ homogeniseHetRedn Representational hreduction

          -- Newtype:
          -----------
          -- NOTE: It is important we first do primitive and user lookups before
          -- unfolding newtypes (i.e. the ordering of the guards are important).
          -- The primitive and user definitions diverge from the normal Haskell
          -- newtype definition. In all cases, we want the pick primitive and user
          -- definitions over newtypes.
          | Just (tc, args) <- splitTyConApp_maybe ty
          , Just (ty', co) <- instNewTyCon_maybe tc args -> do
            mkReductionCast $ mkReduction co ty'

          -- Algebraic Data Type:
          -----------------------
          | Just (tc, args) <- splitTyConApp_maybe ty
          , or $ fmap ($ tc)
            [ isDataTyCon
            , isUnboxedTupleTyCon
            , isUnboxedSumTyCon
            ]
          , Just dataCons <- tyConDataCons_maybe tc -> if
            -- TODO: I really, really hate this level of indentation!
            | isEnumerationTyCon tc -> do
              -- FIXME: This should get the proper platform size.
              let tag = symbolicVar @(SymBitVec 64) var Tag

              -- Tag is within bounds. Note that we only need to check the
              -- upper bound, as the lower bound 0 is already captured by the
              -- fact that the tag is unsigned.
              let upper = fromIntegral $ tyConFamilySize tc
              let inBounds = tag .< upper

              -- Construct the data constructor and its type arguments.
              let dc = pure $ mkCon (EnumCon tag tc)
              mrgIf inBounds dc mkUnreachable

            -- Create cascading if for all possible cases. Note, we avoid
            -- Unreachable at the root, as it would introduce obsolute
            -- constraints.
            | (dcN : dcs) <- reverse dataCons -> do
              let goDataCon dc = do
                    let fieldTys = scaledThing <$> dataConInstArgTys dc args
                    let valArgs = zip [0..] fieldTys <&> \(idx, ty') -> go var
                          { varType = ty'
                          , varAccessor = Accessor dc idx : varAccessor var
                          }

                    let dc' = mkCon $ DataCon dc
                    let tyArgs = pure . mkType <$> args
                    mkApps dc' $ tyArgs <> valArgs

              foldlBy (goDataCon dcN) dcs \acc dc -> do
                let scrut = symbolicVar var $ Select dc
                let expr = goDataCon dc
                mrgIte scrut expr acc

            -- Unreachable otherwise.
            | otherwise -> mkUnreachable

            -- NOTE: I'll leave this todo here for now, because I think the stuff
            -- in here should become a detailed comment at some point in the
            -- future on why we create these values in certain ways.
            --
            -- It would be good to note that we don't use tag at all in non-enum
            -- data con. That is, it is just an fold using boolean conditions:
            -- ite isDC0 DC0 (ite isDC1 DC1 ...)
            --
            -- I guess since we now fully swap to an EnumCon/DataCon sum, this is
            -- probably a bit more obvious. Still, it is good to mention!
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
            --
            -- Another thing: we don't really need the Unreachable case in a
            -- normal (non-enumeration) TyCon. They're encoded as e.g.
            -- ite
            --   (tag == 0)
            --   Just
            --   (ite
            --     (tag == 1)
            --     Nothing
            --     Unreachable)
            -- However, it would make more sense to just write:
            -- ite cond Just Nothing
            --
            -- Where 'cond' is just any conditional. It doesn't need to check
            -- anything about bitvectors! We never use the tag elsewhere! Hmm,
            -- I guess the nice thing about bitvectors is that they make the other
            -- cases exclusive by default. I.e. tag == 0 and tag == 1 are mutually
            -- exclusive, cond1 and cond2 aren't and putting extra conditions like
            -- that is not better than having the unreachable...
            --
            -- Actually, there is an implied order due to the cascading anyway,
            -- so I'm not sure it matters.
            --
            -- It is especially bad for types with a single datacon:
            -- ite
            --   (tag == 0)
            --   I# ...
            --   Unreachable
            --
            -- Why?? :(
            --
            -- I guess we can use the unreachable for DataCon without constructors
            -- like Void? Otherwise, we have no value for it.
            --
            -- For enum TyCon, we of course do plan to use it, so there we do need
            -- the Unreachable statement.

          -- TODO: Throw proper error!
          | otherwise -> do
            dbgE ["could not create fresh value for", ppr ty]
            throwE ()

  go Variable
    { varName = GHC.varName root
    , varAccessor = []
    , varType = GHC.varType root
    , varArgs = []
    }

freshArgs
  :: HasCallStack
  => Error () :> es
  => Context Reader BuiltInTyCon :> es
  => HasFamInstEnvs :> es
  -- TODO: This TyConEnv argument is unclear on what it is. Maybe we could use
  -- a type alias as it is an TypeAxiomR.
  => TyConEnv TyCon
  -> Type
  -> InScopeSet
  -> ([(Var, Arg es)], InScopeSet)
freshArgs axioms ty scope0 = do
  -- Gather the argument types.
  let (tyVars, funTy) = splitForAllTyVars ty
  let (argTys, _resTy) = splitFunTys funTy

  -- TODO: Isn't there some infinite sequence of names that could be used
  -- instead of this?
  -- Names for the arguments.
  let names = repeat "arg"

  -- Create fresh type arguments.
  let kinds = zip names $ fmap tyVarKind tyVars
  let (tyArgs, scope1) = freshTyVars kinds scope0

  -- Create fresh value arguments.
  let types = zip names argTys
  let (valArgs, scope2) = freshIds types scope1

  -- Collection of all arguments.
  let args = tyArgs <> valArgs

  -- Create symbolic instance of the arguments.
  let symbolic = freshExpr axioms <$> args

  -- Zip the binders together with their symbolic instance.
  let binders = zip args symbolic

  -- Return the binders and the new scope.
  (binders, scope2)
