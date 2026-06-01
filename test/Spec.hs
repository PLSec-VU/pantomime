{-# OPTIONS_GHC -fplugin=Pantomime #-}
{-# LANGUAGE BlockArguments #-}

module Main
  ( main
  ) where

import Test.Hspec
import Test.Hspec.Expectations (expectationFailure)

import Pantomime
import Pantomime.BuiltIn qualified as Pantomime

-- =============================================================================
-- Test Case Definitions
-- =============================================================================

-- | Peirce's Law: ((p -> q) -> p) -> p.
-- This is a classical logic tautology that is non-trivial to prove/recognize.
{-# ANN validAssertion (Theory mempty) #-}
validAssertion :: Bool -> Bool -> Pantomime.Bool
validAssertion p q =
  let p' = Pantomime.boolean p
      q' = Pantomime.boolean q
  in ((p' `Pantomime.implies` q') `Pantomime.implies` p') `Pantomime.implies` p'

-- | Fallacy of Affirming the Consequent: ((p -> q) ∧ q) -> p.
-- This is invalid: if p is False and q is True, the premise holds but the conclusion is False.
{-# ANN invalidAssertion (Theory mempty) #-}
invalidAssertion :: Bool -> Bool -> Pantomime.Bool
invalidAssertion p q =
  let p' = Pantomime.boolean p
      q' = Pantomime.boolean q
      (&&.) = (Pantomime.&&)
  in ((p' `Pantomime.implies` q') &&. q') `Pantomime.implies` p'

-- =============================================================================
-- Test Suite
-- =============================================================================

main :: IO ()
main = hspec $ do
  describe "Pantomime Symbolic Checker Unit Tests" $ do
    it "verifies validAssertion (should succeed with Nothing)" $ do
      $(pantomime 'validAssertion) `shouldBe` Nothing

    it "detects invalidAssertion (should fail with Just counterexample)" $ do
      checkInvalid $(pantomime 'invalidAssertion)

-- | Assert that a counterexample was found and print it.
checkInvalid :: Maybe String -> Expectation
checkInvalid = \case
  Just ce -> do
    putStrLn ""
    putStrLn "Counterexample found:"
    putStrLn ce
    putStrLn ""
  Nothing -> expectationFailure "Expected a counterexample but assertion was valid"
