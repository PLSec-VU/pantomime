module Symbolic.Environment
  ( Environment (..)
  , emptyEnv
  , lookupIdEnv
  , extendEnv
  , extendManyEnv
  , substTyEnv
  , substCoEnv
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.Core.Type (substTy)

import Control.Monad (foldM)
import Control.Monad.Except (MonadError (..))
import Control.Applicative (Alternative(..))

import Symbolic.Value
import Symbolic.Util
import Symbolic.MonadEval

-- TODO: Add comments to this module! In short, an environment is like a Subst,
-- but for symbolic lookups.
data Environment m ws = Environment
  { idSubst :: IdEnv (Value m ws)
  , tvSubst :: TvSubstEnv
  , cvSubst :: CvSubstEnv
  }

emptyEnv :: Environment m ws
emptyEnv = Environment
  { idSubst = emptyVarEnv
  , tvSubst = emptyVarEnv
  , cvSubst = emptyVarEnv
  }

lookupIdEnv
  :: MonadError EvalError m
  => Environment m ws
  -> Var
  -> m (Value m ws)
lookupIdEnv env var = whyFail UnboundVariable $ if
  | isTyVar var -> Ty <$> lookupVarEnv (tvSubst env) var
  | isCoVar var -> Co <$> lookupVarEnv (cvSubst env) var
  | isNonCoVarId var -> lookupVarEnv (idSubst env) var
  | otherwise -> empty

extendEnv
  :: MonadError EvalError m
  => Environment m ws
  -> Var
  -> Value m ws
  -> m (Environment m ws)
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
  _ -> throwError IllTyped

extendManyEnv
  :: MonadError EvalError m
  => Foldable t
  => Environment m ws
  -> t (Var, Value m ws)
  -> m (Environment m ws)
extendManyEnv = foldM $ \env (var, value) -> extendEnv env var value

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
