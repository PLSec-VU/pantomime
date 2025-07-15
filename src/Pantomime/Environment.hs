module Pantomime.Environment
  ( Environment (..)
  , emptyEnv
  , lookupLocalEnv
  , extendLocalEnv
  , lookupIdEnv
  , extendEnv
  , extendManyEnv
  , substTyEnv
  , substCoEnv
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Type (substTy)

import Control.Monad (foldM)
import Control.Applicative (Alternative(..))

import Pantomime.Value
import Pantomime.Util
import Pantomime.MonadEval

import Effectful
import Effectful.Error.Static

-- TODO: Add comments to this module! In short, an environment is like a Subst,
-- but for symbolic lookups.
data Environment es ws = Environment
  { idSubst :: IdEnv (Value (Eff es) ws)
  , tvSubst :: TvSubstEnv
  , cvSubst :: CvSubstEnv
  , localIds :: IdEnv CoreExpr
  }

emptyEnv :: Environment es ws
emptyEnv = Environment
  { idSubst = emptyVarEnv
  , tvSubst = emptyVarEnv
  , cvSubst = emptyVarEnv
  , localIds = emptyVarEnv
  }

lookupLocalEnv
  :: Environment es ws
  -> Var
  -> Maybe CoreExpr
lookupLocalEnv env = lookupVarEnv (localIds env)

extendLocalEnv
  :: Environment es ws
  -> CoreProgram
  -> Environment es ws
extendLocalEnv = foldl' $ \env -> \case
  NonRec bndr expr -> do
    let local = extendVarEnv (localIds env) bndr expr
    env { localIds = local }
  Rec _ -> env

lookupIdEnv
  :: Error EvalError :> es
  => Environment es ws
  -> Var
  -> Eff es (Value (Eff es) ws)
lookupIdEnv env var = whyFail UnboundVariable $ if
  | isTyVar var -> Ty <$> lookupVarEnv (tvSubst env) var
  | isCoVar var -> Co <$> lookupVarEnv (cvSubst env) var
  | isNonCoVarId var -> lookupVarEnv (idSubst env) var
  | otherwise -> empty

extendEnv
  :: Error EvalError :> es
  => Environment es ws
  -> Var
  -> Value (Eff es) ws
  -> Eff es (Environment es ws)
extendEnv env var = \case
  Ty ty | isTyVar var -> pure $ env
    { tvSubst = extendVarEnv (tvSubst env) var ty
    }
  Co co | isCoVar var -> pure $ env
    { cvSubst = extendVarEnv (cvSubst env) var co
    }
  value | isNonCoVarId var -> pure $ env
    { idSubst = extendVarEnv (idSubst env) var value
    }
  _ -> throwError_ IllTyped

extendManyEnv
  :: Error EvalError :> es
  => Foldable t
  => Environment es ws
  -> t (Var, Value (Eff es) ws)
  -> Eff es (Environment es ws)
extendManyEnv = foldM \env (var, value) -> extendEnv env var value

envToSubst :: Environment m ws -> Subst
envToSubst env = Subst emptyInScopeSet emptyVarEnv (tvSubst env) (cvSubst env)

substTyEnv
  :: Environment m ws
  -> Type
  -> Type
substTyEnv = substTy . envToSubst

substCoEnv
  :: Environment m ws
  -> Coercion
  -> Coercion
substCoEnv = substCo . envToSubst
