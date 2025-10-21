{-# LANGUAGE OverloadedStrings #-}
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

import GHC.Plugins
  ( CoreProgram
  , Name
  , CoreExpr
  , exprType
  , varType
  , vcat
  , emptyInScopeSet
  )
import GHC.Utils.Outputable
  ( Outputable (..)
  , IsLine (..)
  , SDoc
  , (<+>)
  )

import Grisette (LogicalOp (..), EvalSym (..), onUnion)

import Control.Monad.Except (runExceptT)

import Data.Foldable (for_)

import Language.Haskell.TH qualified as TH

import Pantomime.Expr qualified as Pantomime
import Pantomime.Symbolise qualified as Pantomime
import Pantomime.Subst qualified as Pantomime
import Pantomime.Fresh qualified as Pantomime
import Pantomime.Primitive.GHC qualified as Primitive
import Pantomime.Result (handle, ok)
import Pantomime.Util (withCallStack, dbg)
import Pantomime.Axiom (PluginAxiomsR (..))


import Effectful
import Effectful.Context
import Effectful.Error.Static
import Effectful.GHC.TyThing
import Effectful.GHC.TH
import Effectful.GHC.External
import Effectful.Grisette.Solver
import Effectful.Provider
import Effectful.Exception (ErrorCall (..), throwIO)

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
-- TODO: I should remove this early error catch. Also, these errors are very
-- non-proper. We should throw errors that actually inform us about something!
checkValid PluginAxiomsR { .. } expr = do
  -- TODO: Somehow this code doesn't read very nice. I think I should review it.
  program <- get @CoreProgram

  reifiedIntN <- Primitive.reifiedIntN

  let subst = do
        subst0 <- Pantomime.extendIdSubstMany Pantomime.mkEmptySubst reifiedIntN
        -- TODO: I think there is an ordering problem here between user
        -- mappings and program definitions. I guess user mappings should
        -- go first? The problem is that we don't want local definitions to
        -- overwrite them. I guess for now, we can keep the ordering like this,
        -- but this essentially restricts mappings to be used only outside of
        -- their defining module. Not the worst thing though, as the functions
        -- should truly be opaque outside of the defining module and they cannot
        -- be guaranteed to not be misused within the module.
        let symAxioms = Pantomime.symbolise subst0 <$> termAxiomsR
        let subst1 = Pantomime.extendIdSubstDirectly subst0 symAxioms
        Pantomime.symboliseBindMany subst1 program

  subst' <- case handle subst of
    Left (cs, ()) -> withCallStack cs throwError_ ()
    Right value -> pure $ ok value

  famInst <- getFamInstEnvs
  primTys <- Primitive.getTypes

  let freshEnv = Pantomime.FreshInstEnv
        { Pantomime.fieFam = famInst
        , Pantomime.fiePrim = primTys
        , Pantomime.fieUser = typeAxiomsR
        }

  let ty = exprType expr
  let (args, _scope) = Pantomime.freshArgs freshEnv ty emptyInScopeSet
  let fun = Pantomime.symbolise subst' expr
  let result = fun >>= flip Pantomime.mkApps (snd <$> args)

  -- TODO: I was thinking of making a 'handleE' function for 'Eval', but it
  -- seems like the 'Raise' constructor prohibits this (as it also contains
  -- an error field). Still, I feel like there should be a better way to
  -- construct this...
  let Pantomime.Eval boolResult = result >>= Pantomime.exprToBool
  evalBool <- case handle boolResult of
    Left (cs, ()) -> withCallStack cs throwError_ ()
    Right value -> pure $ runExceptT (ok value)

  let eq = flip onUnion evalBool \case
        Left Pantomime.Unreachable -> true
        Left Pantomime.UB -> false
        Left Pantomime.Raise {} -> false
        Right value -> value

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
  case solution of
    Satisfiable model -> do
      -- TODO: I should probably check whether the arguments are recursive
      -- before printing? Alternatively, I could just have a maximum depth.
      for_ args \(bndr, arg) -> do
        let arg' = evalSym True model arg
        dbg $ vcat
          [ "==================="
          , ppr bndr <+> "::" <+> ppr (varType bndr)
          , ppr arg'
          ]
      error "Expression was **not** valid!"
    Unsatisfiable -> do
      dbg @SDoc "Expression was valid!"
      pure ()
    -- FIXME: I don't think this is always true. Especially so w.r.t. allowing
    -- user define Opaque types. Also not sure about some of the floating point
    -- stuff for example.
    Unknown -> throwIO $ ErrorCall "checks are in decidable fragment"
