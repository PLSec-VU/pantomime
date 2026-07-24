{-# LANGUAGE OverloadedStrings #-}

module Pantomime.Axiom
  ( Embeddings (..)
  , ArgType (..)
  , EmbeddingsR (..)
  , TypeAxiomsR
  , TermAxiomsR
  , resolveEmbeddings
  ) where

import Prelude hiding (break)
import Language.Haskell.TH qualified as TH

import GHC.Core.InstEnv (mkLocalClsInst, emptyInstEnv, extendInstEnv)
import GHC.Core.TyCo.Rep (UnivCoProvenance (..), Coercion (..))
import GHC.Core.TyCon.Env (TyConEnv)
import GHC.Core.Unfold.Make (mkDFunUnfolding)
import GHC.Plugins
  ( TyCon (..)
  , Name
  , Id
  , CoreExpr
  , CoreProgram
  , Role (..)
  , Expr (..)
  , Var (..)
  , Type
  , MonadUnique (..)
  , OverlapFlag (..)
  , OverlapMode (..)
  , TyVar
  , Unique
  , mkTyConTy
  , mkUnivCo
  , dataConWorkId
  , mkApps
  , mkAppTy
  , mkTyVarTy
  , mkVarOccFS
  , mkSystemName
  , mkTyVar
  , classDataCon
  , typeKind
  , coercibleDataCon
  , generatedSrcSpan
  , setIdUnfolding
  , splitFunTy_maybe
  , isTypeSynonymTyCon
  , mkFastString
  , expandTypeSynonyms
  , splitTyConAppNoView_maybe
  , unitDataConId
  )
import GHC.Tc.Utils.TcType (eqType)
import GHC.Types.Id.Make (mkDictFunId)
import GHC.Types.Name (mkInternalName)
import GHC.Utils.Outputable
  ( Outputable (..)
  , IsDoc (..)
  , IsLine (fsep, (<+>), text, hcat)
  , SDoc
  , hang
  , punctuate
  , comma
  , brackets
  , parens
  )
import GHC.Types.SourceText (SourceText(..))
import GHC.Types.Unique (incrUnique, minLocalUnique)

import Control.Monad ((>=>), unless)

import Data.Data (Data)
import Data.Foldable (for_)
import Data.Generics.Aliases (mkQ)
import Data.Generics.Schemes (something)
import Data.HashMap.Internal.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.List (sort)
import Data.Text (Text, unpack)
import Data.Traversable (for)

import Effectful
import Effectful.Break (runBreak, break)
import Effectful.Error.Static
import Effectful.GHC.TH
import Effectful.GHC.TyThing
import Effectful.GHC.Unique (HasUnique)
import Effectful.Context

import Pantomime.BuiltIn (Embeddable, Embedding (..))
import Pantomime.Unification (subsumeExpr)
import Pantomime.Util (foldM', dbg, failWith)

-- TODO: This should be renamed to 'Embeddings' instead of 'Axioms'. We can
-- probably drop the 'Plugin' portion as well.
-- kinded types: something we don't care about within the evaluator. Instead,
-- we provide a custom typeclass. The comments should mirror this!
-- TODO: The text below should be updated to reflect the current state of
-- embeddings. We should at some point link the paper also.
-- | User axioms only visible to the plugin.
--
-- The kinds and types of the mapped terms should match up exactly. The
-- exception is that type-level axioms will be used to instantiate requirements
-- of 'Embeddable' on any term-level axiom.
--
-- # Example
--
-- Suppose the user has some bitvector type called 'IntN'.
--
-- > type IntN (n :: Nat) = ...
--
-- The user supplies the following mapping:
--
-- > IntN |-> BitVec
--
-- This roughly says that the user wants to use the underlying bitvector
-- representation 'BitVec'. 'BitVec' is treated as a primitive within the plugin
-- and is implemented using the respective SMT theory. A mapping between
-- non-primitive types is also allowed (or any mixing of these, use type aliases
-- for this).
--
-- Now, a user has some functions that operate on 'IntN'. These of course
-- require a mapping to the their respective operation on 'BitVec'. Before
-- anything, a user needs to ensure that **ALL** operations on 'IntN' are
-- through functions marked as 'OPAQUE' and that it's constructor is not
-- exported. This is to ensure correctness within the evaluator, as otherwise
-- representational equivalence is broken.
--
-- With this in mind, the following will illustrate how to write an
-- interpretation. Suppose we have an addition function for 'IntN' values.
--
-- > {-# OPAQUE plusIntN #-}
-- > plusIntN :: KnownNat n => IntN n -> IntN n -> IntN n
--
-- We can write an interpretation for this using the addition as provided by
-- 'BitVec'. The importance lies in using a coercion 'Coercible IntN BitVec'.
--
-- > plusInterp
-- >   :: Embeddable bv BitVec
-- >   => KnownNat n
-- >   => bv n
-- >   -> bv n
-- >   -> bv n
-- > plusInterp = case embedding @bv @BitVec of
-- >   Embedding -> coerce SMT.bvadd
--
-- Note, the where clause is only to trick Haskell into allowing the coercion
-- to appear at the top level. With this defintion in place, we supply the
-- appropriate mapping:
--
-- > plusIntN |-> plusInterp
--
-- Of course, the types for 'plusIntN' and 'plusInterp' do not match up
-- one-to-one. That is, to complete the interpretation, we supply 'plusInterp'
-- with the user-supplied coercion that 'Coercible IntN BitVec'. Afterwards, the
-- types match up and the function is a valid interpretation.
data Embeddings where
  Embeddings ::
    -- TODO: Probably want to remove the comment about fresh symbolic values
    -- once we change the interface on this.
    { typeEmbeddings :: [(ArgType, ArgType)]
    -- ^ Type-level embeddings.
    --
    -- Both the key and value of these mappings should be resolvable to a GHC
    -- 'Type'. One may think about this as providing an instance 'Embeddable'
    -- to the plugin between for the given types. This instance is used within
    -- the solver when constructing fresh symbolic values and when resolving
    -- instances for term-embeddings.
    -- TODO: Term axioms should allow for recursive definitions also. It
    -- probably won't be used much, but it would be good! I guess we would want
    -- a 'Bind' from GHC, but for template haskell names.
    -- Actually, the above is not really required I think: the embedding can
    -- always form a local recursive group. Will have to think about this!
    , termEmbeddings :: [(TH.Name, TH.Name)]
    -- ^ Term-level representational equivalence axioms.
    --
    -- Both the key and value of these mappings should be resolvable to 'Id'.
    -- This can be used to operate on types that have user-provided equivalence
    -- axioms via 'typeAxioms'. The types should match exactly between both
    -- 'Id's, with the exception of 'Coercible' instances that may be resolved
    -- using the 'typeAxioms'.
    --
    -- Note that this is a list because the ordering of the definitions does
    -- matter: any later definitions may use ones defined earlier. Duplicate
    -- definitions are considered an error.
    } -> Embeddings
  deriving (Show, Data)

instance Outputable Embeddings where
  ppr Embeddings { .. } = do
    let pprKV (key, value) = text (show key) <+> ":->" <+> text (show value)
    let pprKVList pairs = brackets $ fsep $ punctuate comma $ pprKV <$> pairs
    hang "Embeddings" 2 $ vcat
      [ hang "Type Embeddings:" 2 $ pprKVList typeEmbeddings
      , hang "Term Embeddings:" 2 $ pprKVList termEmbeddings
      ]

instance Semigroup Embeddings where
  (<>) l r = Embeddings
    { typeEmbeddings = typeEmbeddings l <> typeEmbeddings r
    , termEmbeddings = termEmbeddings l <> termEmbeddings r
    }

instance Monoid Embeddings where
  mempty = Embeddings
    { typeEmbeddings = mempty
    , termEmbeddings = mempty
    }

type TypeAxiomsR = TyConEnv TyCon

-- TODO: I guess these might be better suited as CoreBind no?
type TermAxiomsR = [(Id, CoreExpr)]

-- TODO: I think it would be good to have type synonyms for both of these fields
-- as we use them independently as well.
-- | Fully resolved plugin axioms. These may be used as-is by the solver.
data EmbeddingsR where
  EmbeddingsR ::
    { typeAxiomsR :: TypeAxiomsR
    -- ^ Type-level axioms, mainly used to construct symbolic values.
    , termAxiomsR :: TermAxiomsR
    -- ^ Term-level axioms, these already have their 'Coercible' instances
    -- resolved by the type-axioms, where applicable.
    --
    -- This may be used to extend substitution environments.
    } -> EmbeddingsR

instance Outputable EmbeddingsR where
  ppr EmbeddingsR { .. } = hang "EmbeddingsR" 2 $ vcat
    [ hang "Type Embeddings:" 2 $ ppr typeAxiomsR
    , hang "Term Embeddings:" 2 $ ppr termAxiomsR
    ]

instance Semigroup EmbeddingsR where
  (<>) l r = EmbeddingsR
    -- { typeAxiomsR = unionInstEnv (typeAxiomsR l) (typeAxiomsR r)
    { typeAxiomsR = typeAxiomsR l <> typeAxiomsR r
    , termAxiomsR = termAxiomsR l <> termAxiomsR r
    }

instance Monoid EmbeddingsR where
  mempty = EmbeddingsR
    -- { typeAxiomsR = emptyInstEnv
    { typeAxiomsR = mempty
    , termAxiomsR = mempty
    }

-- | A restricted form of types used for user defined 'Embeddable' instances.
data ArgType where
  ATApp :: ArgType -> ArgType -> ArgType
  ATCon :: TH.Name -> ArgType
  ATVar :: Text -> ArgType -> ArgType
  deriving (Show, Data)

instance Outputable ArgType where
  ppr = do
    let go par = \case
          ATApp fun arg -> par $ go id fun <+> go parens arg
          ATCon con -> text $ show con
          ATVar var _kind -> text $ unpack var
    go id

-- | Variable store, used to track variable occurences and create new ones.
--
-- NOTE: As the uniques in the TyVar's are just incremented local Unique values,
-- we can get a deterministic order of their occurence by sorting based on the
-- Unique.
type VarStore = (HashMap Text TyVar, Unique)

-- | Reify an 'ArgType' for a typeclass instance into a full Haskell type.
--
-- The 'Unique' on the 'TyVar' in the 'VarStore' can be sorted for a
-- deterministic declaration order for the type variables.
reifyArgType
  :: HasCallStack
  => Error SDoc :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => Context Reader [TyCon] :> es
  => Context Writer VarStore :> es
  => Context Reader VarStore :> es
  => ArgType
  -> Eff es Type
-- TODO: Fix call stack growth.
reifyArgType = \case
  ATApp fun arg -> do
    -- Get function type and check if has a function kind.
    fun' <- reifyArgType fun
    let err = "Type application function does not have function kind."
    (_, _, farg, _) <- failWith @SDoc err $ splitFunTy_maybe (typeKind fun')

    -- Get the argument and check if its kind mathes the function argument.
    arg' <- reifyArgType arg
    unless (eqType farg $ typeKind arg') do
      throwError_ @SDoc "Argument kind does not equal expected kind."

    -- Return the application.
    pure $ mkAppTy fun' arg'

  ATCon name -> do
    name' <- thNameToGhcName name
    tc <- lookupTyConAll name'
    pure $ mkTyConTy tc

  ATVar name kind -> runBreak do
    -- Fetch the variable store.
    (mapping, unique) <- get @VarStore

    -- Reify the kind of the variable.
    kind' <- reifyArgType kind

    -- Early break if we already have a type variable for the name.
    let existing = HashMap.lookup name mapping
    for_ existing \tv -> do
      let kind2 = varType tv
      unless (eqType kind' kind2) do
        throwError_ @SDoc $ hcat
          [ "Type variable '"
          , text $ unpack name
          , "' occurs with different kinds '"
          , ppr kind'
          , "' and '"
          , ppr kind2
          , "'"
          ]
      break $ mkTyVarTy tv

    -- Create the fresh type variable.
    let occ = mkFastString $ unpack name -- TODO: Not the best conversion...
    let name' = mkSystemName unique $ mkVarOccFS occ
    let tv = mkTyVar name' kind'

    -- Extend the store with the type variable and increment the unique.
    let mapping' = HashMap.insert name tv mapping
    let unique' = incrUnique unique
    put (mapping', unique')

    -- Return the type variable.
    pure $ mkTyVarTy tv

-- | Finds a type synonym in a 'Type'.
hasSynonym :: Type -> Maybe TyCon
hasSynonym = something $ mkQ Nothing \ty -> do
  case splitTyConAppNoView_maybe ty of
    Just (tc, _) | isTypeSynonymTyCon tc -> Just tc
    _ -> Nothing

-- | Expand all type synonyms from a type.
--
-- Throws an error if any type synonym still remains.
expandTypeSynonyms'
  :: Error SDoc :> es
  => Type
  -> Eff es Type
expandTypeSynonyms' ty = do
  let ty' = expandTypeSynonyms ty
  case hasSynonym ty' of
    Just tc -> throwError_ @SDoc $ hcat
      [ "Type '"
      , ppr ty'
      , "' contains unsaturated type constructor '"
      , ppr tc
      , "' after type alias expansion."
      ]
    Nothing -> pure ()
  pure ty'

-- | Resolve user-supplied axioms in terms of Template Haskell names to their
-- internal Core representation.
--
-- Check 'PluginAxiom' for a more detailed explanation of user axioms.
--
-- In short, this function will resolve the Template Haskell names to their
-- respective TyCon, Id or CoreExpr. Afterwards, it will supply any 'Coercible'
-- instance as provided by the type-level axioms. The modified 'CoreExpr' is
-- then checked to match exactly the type of the 'Id' that maps to it to ensure
-- correctness.
--
-- Lastly, this also ensures that mappings are only made for OPAQUE functions.
-- A special case here we do allow is a NOINLINE function without an unfolding.
-- For these, we do not use any of the user-provided coercions.
resolveEmbeddings
  :: HasCallStack
  -- TODO: Adjust these errors!
  => Error String :> es
  => Error SDoc :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => THNameToGHCName :> es
  => HasThings :> es
  => HasUnique :> es
  => Context Reader CoreProgram :> es
  => Context Reader [TyCon] :> es
  => Embeddings
  -> Eff es EmbeddingsR
resolveEmbeddings Embeddings { .. } = do
  -- Get the typeclass we want to instantiate.
  embeddable <- thNameToGhcName >=> lookupClass $ ''Embeddable
  embedding <- thNameToGhcName >=> lookupDataCon $ 'Embedding

  -- Gather the instance environment for resolution.
  instEnv <- foldM' emptyInstEnv typeEmbeddings \instEnv (tyL, tyR) -> do
    -- Reify the instance head into GHC Types.
    let runReify = runContextLocal @VarStore (mempty, minLocalUnique)
    ((tyL', tyR'), store') <- runReify do
      tyL' <- reifyArgType tyL
      tyR' <- reifyArgType tyR
      pure (tyL', tyR')

    -- Expand the type synonyms in the types.
    tyL'' <- expandTypeSynonyms' tyL'
    tyR'' <- expandTypeSynonyms' tyR'

    -- FIXME: We should ensure that the kinds for the type match up
    -- (up to runtime representation).

    -- Gather the information to construct the coercion.
    let prov = PluginProv "sym-fc embedding (user-defined)"
    let kindL = typeKind tyL''
    let kindR = typeKind tyR''
    let co = mkUnivCo prov [] Representational tyL'' tyR''

    -- Create a unique name for the embedding.
    unique <- getUniqueM
    let occ = mkVarOccFS "embedding"
    let name = mkInternalName unique occ generatedSrcSpan

    -- Type variables used in the instance declaration.
    -- NOTE: We can sort the type variables by Unique to get the declaration
    -- order per 'reifyArgType'.
    let tvs = sort $ HashMap.elems (fst store')

    -- We don't support typeclass requirements (not sure if we ever need them)?
    let theta = []

    -- Construct the initial 'DFunId', without unfolding.
    let tys = [kindL, kindR, tyL'', tyR'']
    let dfun = mkDictFunId name tvs theta embeddable tys

    -- Create the 'Coercible' dictionary.
    let coercibleDict = mkApps (Var $ dataConWorkId coercibleDataCon)
          [ Type kindL
          , Type tyL''
          , Type tyR''
          , Coercion co
          ]

    -- Create the 'Embedding' data type.
    let coK = mkUnivCo prov [] Nominal kindL kindR
    let embed = mkApps (Var $ dataConWorkId embedding)
          [ Type kindL
          , Type kindR
          , Type tyL''
          , Type tyR''
          , Type tyR''
          , Coercion coK
          , Coercion $ Refl tyR''
          , coercibleDict
          ]

    -- The 'Embeddable' typeclass has a 'PrivateEmbeddable' requirement that is
    -- there just so users cannot create an instance manually. It is essentially
    -- a unit value with a different type, so we just pass in a unit as it is
    -- never used. Slightly hacky, but it works (we cannot create the instance
    -- correctly as it is not exported).
    let private = Var unitDataConId

    -- Create the 'DFunUnfolding'.
    let bndrs = []
    let dc = classDataCon embeddable
    let args = [Type kindL, Type kindR, Type tyL'', Type tyR'', private, embed]
    let unfolding = mkDFunUnfolding bndrs dc args

    -- Set the unfolding of the 'DFunId'.
    let dfun' = setIdUnfolding dfun unfolding

    -- Create the local typeclass instance.
    let overlap = OverlapFlag
          { overlapMode = NoOverlap NoSourceText
          , isSafeOverlap = False
          }
    let warn = Nothing
    let inst = mkLocalClsInst dfun' overlap tvs embeddable tys warn

    -- Extend the instance environment with the embedding.
    pure $ extendInstEnv instEnv inst

  dbg instEnv

  -- TODO: We should first ensure that termAxioms do not contain duplicate
  -- definitions.

  -- Gather a binder mapping for a substitution. This will use the dictionary
  -- map to supply coercions to any Opaque values that require it.
  _termAxiomsR <- for termEmbeddings \(orig, interp) -> do
    -- Resolve the names as identifiers.
    let resolve = thNameToGhcName >=> lookupIdAll
    orig' <- resolve orig
    interp' <- resolve interp

    -- TODO: I'm not sure what to do with this. Should we just always resolve
    -- using the embeddings?
    -- -- Gather the expression of the interpretation.
    -- -- TODO: Should we also attempt to get it from the local bindings?
    -- expr <- case realIdUnfolding interp' of
    --   CoreUnfolding { uf_tmpl } -> pure uf_tmpl
    --   _ -> throwError_ ()

    -- -- Check whether the original target can be interpreted.
    -- dicts' <- case inl_inline $ idInlinePragma orig' of
    --   -- Opaque values can be fully interpreted. Hence, we resolve any coercions
    --   -- that were provided by the user.
    --   Opaque _ -> pure dicts

    --   -- We only want to interpret no-inline if the unfolding was not available.
    --   NoInline _ | not . hasCoreUnfolding $ realIdUnfolding orig' -> do
    --     pure emptyTM

    --   -- It is fragile to interpret inlineable instances, as they may already
    --   -- have been optimised away.
    --   -- FIXME: It seems that the 'noinline' function has a NOINLINE pragma
    --   -- but when testing it here, it doesn't. I feel like this test is the
    --   -- correct one but it doesn't work in this case. I'll leave it like this
    --   -- for now.
    --   --
    --   -- Actually, I ran into an issue where the function I wanted to call had
    --   -- a NOINLINE on an inner value (that was not exported). Perhaps it still
    --   -- makes sense to overwrite definitions, even if they can be inlined? I
    --   -- guess it is still pretty fragile...
    --   -- _ -> throwError_ ()
    --   _ -> pure emptyTM

    -- Check whether the interpretation matches.
    let dicts = undefined
    expr' <- subsumeExpr dicts (Var interp') $ varType orig'

    -- Return the mapping.
    pure (orig', expr')

  -- Collect the resolved type and term mappings.
  pure EmbeddingsR
    { typeAxiomsR = mempty
    , termAxiomsR = mempty
    }
