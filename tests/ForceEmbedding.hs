module ForceEmbeddings
  ( theory
  ) where

-- FIXME: Right now, 'collectScrut' will throw an error if we force a
-- literal. I'm not 100% sure what the behaviour should be, but it
-- definitely shouldn't throw. The only thing I'm not sure about, is
-- what to do with constraints: should they now be part of the outer
-- expression?
--
-- Example faulting expression. I was not able to reproduce it for a
-- different type than an embedded Array type... I think it's due to
-- the way it is embedded (that is, it is a 'Cast' at the outer layer).
{-# NOINLINE test #-}
test :: Memory -> Pantomime.Bool
test !_ = Pantomime.True

{-# ANN theory (Theory $ Base.axioms <> Clash.axioms <> RISCV.axioms) #-}
theory :: Pantomime.Bool
theory = test $ constM 0
