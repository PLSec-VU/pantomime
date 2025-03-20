module Monomorph 
  ( monomorphize
  ) where

import GHC.Plugins hiding (empty, (<>))
import GHC.MonadCore

-- import Control.Applicative (Alternative (..), empty)
import Control.Monad.Reader (ReaderT (..))

import Lens.Micro

import Transform
import Types
import qualified Lint
import qualified Subst

monomorphize
  :: MonadCore m
  => HasDynFlags m
  => ModGuts
  -> Pass m CoreExpr
monomorphize guts expr = do
  rules <- liftCore $ initRuleEnv guts
  let runPass = flip runReaderT rules

  let passes =
        [ inlineUnfolding
        , betaReduce
        , caseReduce
        , dropReflCast
        , joinCasts
        , floatCast
        , applyRule
        ]

  -- Run passes on the expression until saturation.
  let subst = initSubst $ mg_binds guts :: Subst
  expr' <- runPass $ saturate passes subst expr
  Lint.panic Lint.full (subst ^. Subst.scope) expr'
  pure expr'

-- betaReduceMono
--   :: Monad m
--   => Alternative m
--   => Subst.Class s
--   => Transform m s CoreExpr
-- betaReduceMono continue subst = \case
--   -- Normal beta reduction.
--   App (Lam bndr body) arg -> case idOccInfo bndr of
--     _ | isTyVar bndr -> reduce body bndr arg
--     _ | isOneShotInfo $ idOneShotInfo bndr -> reduce body bndr arg
--     OneOcc { occ_in_lam = NotInsideLam, occ_n_br = 1 } -> reduce body bndr arg
--     IAmDead -> reduce body bndr arg
--     _ -> empty

--   -- Reduction on let binding.
--   Let (NonRec bndr expr) body -> case idOccInfo bndr of
--     _ | isTyVar bndr -> reduce body bndr expr
--     _ | isOneShotInfo $ idOneShotInfo bndr -> reduce body bndr expr
--     OneOcc { occ_in_lam = NotInsideLam, occ_n_br = 1 } -> reduce body bndr expr
--     IAmDead -> reduce body bndr expr
--     _ -> empty

--   _ -> empty
--   where
--     reduce body bndr expr = do
--       expr' <- continue subst expr
--       let subst' = subst & Subst.extend bndr expr'
--       continue subst' body
