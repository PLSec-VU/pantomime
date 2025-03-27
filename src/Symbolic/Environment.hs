module Symbolic.Environment
  ( Environment (..)
  , emptyEnv
  , lookupEnv
  , extendEnv
  , extendManyEnv
  ) where

import GHC.Plugins hiding (empty, (<>))

import Control.Monad (foldM)
import Control.Monad.Except (MonadError (..))
import Control.Applicative (Alternative(..))

import Symbolic.Value
import Symbolic.Util
import Symbolic.MonadEval

data Environment m n = Environment
  { idSubst :: IdEnv (Value m n)
  , tvSubst :: TvSubstEnv
  , cvSubst :: CvSubstEnv
  }

emptyEnv :: Environment m n
emptyEnv = Environment
  { idSubst = emptyVarEnv
  , tvSubst = emptyVarEnv
  , cvSubst = emptyVarEnv
  }

lookupEnv
  :: MonadError EvalError m
  => Environment m n
  -> Var
  -> m (Value m n)
lookupEnv env var = whyFail UnboundVariable $ if
  | isTyVar var -> Ty <$> lookupVarEnv (tvSubst env) var
  | isCoVar var -> Co <$> lookupVarEnv (cvSubst env) var
  | isNonCoVarId var -> lookupVarEnv (idSubst env) var
  | otherwise -> empty

extendEnv
  :: MonadError EvalError m
  => Environment m n
  -> Var
  -> Value m n
  -> m (Environment m n)
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
  => Environment m n
  -> t (Var, Value m n)
  -> m (Environment m n)
extendManyEnv = foldM $ \env (var, value) -> extendEnv env var value
