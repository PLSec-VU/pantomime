{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE DeriveGeneric #-}
-- TODO: I want to remove many of these pragmas, also for the other files. Most
-- of them should just be included in the top-level flags. There also seems to
-- be a lot of obsolete stuff. Perhaps its good to first find out which flags
-- are actually used. I actually removed most of them here, but there's still
-- way too many in other files. Isn't there an 'obsolete pragma warning' or
-- something in GHC?

-- TODO: I feel like the pantomime dependencies that are used solely by the
-- final solver should go under Pantomime.Solve.X (e.g. Pantomime.Solve.Value).
-- Right now, the hierarchy is a bit too flat, which makes the project structure
-- a lot less clear. Alternatively, we can use Pantomime.Symbolic.X

module Pantomime.Solve
  ( checkValid
  ) where

import GHC.Core qualified as GHC
import GHC.Core.FamInstEnv (FamInstEnvs)
import GHC.Generics (Generic)
import GHC.Plugins
  ( CoreProgram
  , Name
  , CoreExpr
  , Bind (..)
  , exprType
  , varType
  , vcat
  , emptyInScopeSet, Var
  )
import GHC.Types.Id.Make (nospecId)
import GHC.Utils.Outputable
  ( Outputable (..)
  , IsLine (..)
  , SDoc
  , (<+>)
  )

import Grisette (LogicalOp (..), EvalSym (..), Union, SymBool, onUnion)

import Control.DeepSeq (NFData (..))

import Data.Foldable (for_)
import Data.Traversable (for)

import Language.Haskell.TH qualified as TH

import Pantomime.Expr
  ( Expr (..)
  , Arg
  , Variant (..)
  , Literal (..)
  , mkApps
  , pprArg
  , pprRuntime
  , runRuntime
  , throwE
  )
import Pantomime.Literal (BuiltInTyCon (..))
import Pantomime.Symbolise
import Pantomime.Subst
import Pantomime.Fresh
import Pantomime.Util (dbg)
import Pantomime.Axiom (PluginAxiomsR (..))
import Pantomime.PrimOps (PrimOp)
import Pantomime.Defer (defer, withDeferrable)
import Pantomime.Binding
  ( InterfaceThings
  , getInterfaceThings
  , getBuiltinTyCon
  , bindingsGHC
  )

import Effectful
import Effectful.Context
import Effectful.Error.Static
import Effectful.GHC.TyThing
import Effectful.GHC.TH
import Effectful.GHC.External
import Effectful.Grisette.Solver
import Effectful.Provider
import Effectful.Exception (ErrorCall (..), throwIO)

-- TODO: Definitely not the cleanest place to add these effects. I should look
-- into where to do this.
runBuiltInTypes
  :: Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => HasFamInstEnvs :> es
  => Eff (Context Reader BuiltInTyCon : Context Reader InterfaceThings : Context Reader FamInstEnvs : es) a
  -> Eff es a
runBuiltInTypes eff = do
  tys <- getBuiltinTyCon
  ids <- getInterfaceThings
  fam <- getFamInstEnvs
  runContextReader fam . runContextReader ids . runContextReader tys $ eff

type SymboliseEff =
 '[ Context Reader BuiltInTyCon
  , Context Reader InterfaceThings
  , Context Reader FamInstEnvs
  , Error ()
  ]

newtype Lie a where
  Lie :: a -> Lie a
  deriving Generic

instance NFData (Lie a) where
  rnf _ = ()

construct
  :: HasCallStack
  => Context Reader BuiltInTyCon :> es
  => Context Reader InterfaceThings :> es
  => Context Reader FamInstEnvs :> es
  => Error () :> es
  => [(Var, forall fs. PrimOp fs)]
  -> PluginAxiomsR
  -> CoreProgram
  -> CoreExpr
  -- FIXME: This 'Lie' evades the check NFData constraint on 'withDeferrable'.
  -- I'm not sure how to go around this, so for now we just let it crash if it
  -- does occur.. :/
  -> Eff es (SymBool, Lie (Eff SymboliseEff [(Var, Arg)]))
construct prim PluginAxiomsR { .. } program expr = inject @SymboliseEff $ withDeferrable do
  prim' <- for prim \(bndr, rhs) -> do
    rhs' <- defer rhs
    pure (bndr, rhs')

  -- Create the final substitution.
  subst0 <- extendIdSubstMany mkEmptySubst prim'
  let termAxiomsR' = uncurry NonRec <$> termAxiomsR
  subst1 <- symboliseBindMany subst0 termAxiomsR'
  -- TODO: I think there is an ordering problem here between user
  -- mappings and program definitions. I guess user mappings should
  -- go first? The problem is that we don't want local definitions to
  -- overwrite them. I guess for now, we can keep the ordering like this,
  -- but this essentially restricts mappings to be used only outside of
  -- their defining module. Not the worst thing though, as the functions
  -- should truly be opaque outside of the defining module and they cannot
  -- be guaranteed to not be misused within the module.
  subst <- symboliseBindMany subst1 program

  -- Create fresh arguments.
  let ty = exprType expr
  (args, _scope) <- freshArgs typeAxiomsR ty emptyInScopeSet

  result <- defer do
    fun <- symbolise subst expr
    res <- mkApps fun $ fmap snd args
    case res of
      Lit (Bool value) -> pure value
      _ -> throwE ()

  let doc = pprRuntime (\par -> par . text . show) id result
  dbg doc

  -- TODO: What to do about raise? Do we really just want to return false? I
  -- guess for now it makes sense.
  let eq = flip (onUnion @Union) (runRuntime result) \case
        Left Unreachable -> true
        Left UB -> false
        Left Raise {} -> false
        Right value -> value
  pure (eq, Lie $ pure args)

checkValid
  :: forall es
   . HasCallStack
  => Error () :> es
  => Error (LookupError TH.Name) :> es
  => Error (LookupError Name) :> es
  => Error SolverError :> es
  => Context Reader CoreProgram :> es
  => HasThings :> es
  => THNameToGHCName :> es
  => HasFamInstEnvs :> es
  => Provider_ Solver () :> es
  => PluginAxiomsR
  -> CoreExpr
  -> Eff es ()
checkValid axioms expr = runBuiltInTypes do
  -- TODO: Somehow this code doesn't read very nice. I think I should review it.
  program <- get @CoreProgram

  prim <- bindingsGHC

  -- TODO: Is there perhaps a better place to add this? Ideally we just do it
  -- as a normal axiom, but I cannot find where 'nospec' is defined...
  idId <- thNameToGhcName 'id >>= lookupIdAll
  let axioms' = axioms { termAxiomsR = (nospecId, GHC.Var idId) : termAxiomsR axioms } 

  (eq, Lie args) <- construct prim axioms' program expr

  solution <- provide_ @Solver $ solve (symNot eq)

  -- TODO: Do we not have to assert that the input is never Invalid?
  -- I.e. if we want to prove equivalence between (assuming inputs cannot be
  -- bottom):
  --
  -- ex1 :: Void -> Int
  -- ex1 _ = 0
  --
  -- ex2 :: Void -> Int
  -- ex2 _ = 1
  --
  -- Then we need to pass in the constraint that Void only contains Invalid
  -- as a value.
  --
  -- I guess the expected behaviour in these cases would be that the function
  -- forces the Void value in order to create any value via an empty case. I
  -- don't think in practise we care about this one.
  --
  -- In fact, if the user doesn't force it, it is indeed not the case that these
  -- functions are equivalent (even though I guess for this input, they are).
  case solution of
    Satisfiable model -> do
      -- TODO: I should probably check whether the arguments are recursive
      -- before printing? Alternatively, I could just have a maximum depth.
      args' <- inject args
      for_ args' \(bndr, arg) -> do
        let arg' = evalSym True model arg
        let argdoc = pprArg id arg'
        dbg $ vcat
          [ "==================="
          , ppr bndr <+> "::" <+> ppr (varType bndr)
          , argdoc
          ]
      error "Expression was **not** valid!"
    Unsatisfiable -> do
      dbg @SDoc "Expression was valid!"
      pure ()
    -- FIXME: I don't think this is always true. e.g. not sure about some of the
    -- floating point stuff for example.
    Unknown -> throwIO $ ErrorCall "checks are in decidable fragment"
