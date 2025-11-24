{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-all #-}

module Processor
    ( tickRun,
      simRun,
      leak,
      obs,
      proj,
      diff,
    ) where
--import Test.QuickCheck

import Data.Word
import Data.Bits
import Control.Monad.State (MonadState, MonadIO, put, get, runStateT, runState, liftIO)
import Data.Maybe (isJust)
import Data.Tuple (swap)

--import Test.QuickCheck hiding ((.&.))

data Instruction = Add Word8
                -- ^ Add immediate to the register
                |  Clr
                -- ^ Reset the register to zero
                |  Out 
                -- ^ Output the register value
                deriving (Eq, Ord, Show) 

-- |Instruction encoding schema:
--
-- 16-bit word layout:
-- +--------+--------+
-- | Opcode | Value  |
-- +--------+--------+
-- 15      8 7      0
--
-- Opcode:
-- 00 - Add (with 8-bit immediate value)
-- 01 - Clr
-- 10 - Out
encode :: Instruction -> Word16
encode instruction = case instruction of
    Add value -> (0 `shiftL` 8) .|. fromIntegral value
    Clr       -> 1 `shiftL` 8
    Out       -> 2 `shiftL` 8

decode :: Word16 -> Instruction
decode word = case shiftR word 8 of
    0 -> Add (fromIntegral (word .&. 0xFF))
    1 -> Clr
    2 -> Out
    _ -> Add 0
    -- _ -> error "Invalid instruction"

-- | Processor State
data State = State {
    -- architectural state
    pc :: Word8,
    reg :: Word32,
    -- stalled bit
    stalled :: Bool,
    -- pipeline registers
    fetchInstruction :: Instruction,
    writebackOut :: (Maybe Writeback, Maybe Output)
} deriving (Eq, Show)


newtype Output = Val Word32 deriving (Eq, Show)
newtype Writeback = Write Word32 deriving (Eq, Show)

-- | Pipeline Stages

fetch :: MonadState State m => Word16 -> m ()  -- Updates fetchExecute register
fetch rawInstr = do
    state <- get 
    -- updating execute's new instruction
    if stalled state then return ()
    else do 
        let inst = decode rawInstr
        put $ state {fetchInstruction = inst, pc = pc state + 1}

execute :: MonadState State m => m ()
execute = do 
    state <- get
    let instr = fetchInstruction state
    case instr of
        Add value ->
            -- | stalled or fast-path, execute now.
            if stalled state || value == 0 then do -- || reg state == 0 then do
                let result = Just $ Write $ reg state + fromIntegral value
                put $ state {stalled = False, writebackOut = (result, Nothing)}
            -- | slow-path, stall the pipeline for one tick.                        
            else do
                put $ state {stalled = True, writebackOut = (Nothing, Nothing)}
        Clr ->
                put $ state {stalled = False, writebackOut = (Just (Write 0), Nothing)} 
        Out ->
                put $ state {stalled = False, writebackOut = (Nothing, Just $ Val (reg state))} 

writeback :: MonadState State m => m (Maybe Output, Word8)
writeback = do
        state <- get
        let (wb, out) = writebackOut state
        put state{reg = maybe (reg state) (\(Write v) -> v) wb} 
        return (out, pc state)

tick :: MonadState State m => Word16 -> m (Maybe Output, Word8)
tick rawInst = do
    (out, pc) <- writeback
    execute 
    fetch rawInst
    return (out, pc)

diff :: (State, Word16)
diff = (s, i)
    where
        s = State
            { pc = 0 -- Don't care
            , reg = 0 -- Don't care
            , stalled = False
            , fetchInstruction = Add 0
            , writebackOut = (Nothing, Nothing) -- Don't care about fst
            }
        i = 0xffff

tickRun :: State -> Word16 -> (State, (Maybe Output, Word8))
tickRun s i = swap $ runState (tick i) s

run :: MonadState State m => [Word16] -> m [Maybe Output]
run program = do
    state <- get
    if pc state >= fromIntegral (length program) 
    then return []
    else 
        do
        let inst = program !! fromIntegral (pc state)
        (out, _) <- tick inst
        os <- run program
        return $ out:os

test :: IO ()
test = do
    --quickCheckWith stdArgs { maxSuccess = 2000000 } theorem

    --putStrLn $ "Equal? : " ++ show (theorem prog)
    (outs, s) <- runStateT (run bin) initState
    putStrLn $ "halted, with final state" ++ show s
    putStrLn $ "outputs" ++ show outs
    where 
      --prog = [Out, Add 2, Out, Add 3, Out, Clr, Out]  
      --prog = [Out, Add 2, Out, Clr, Out, Add 3, Out]  
      prog = [Out, Add 1, Out, Add 0, Out, Clr, Out, Add 41, Out, Add 1, Out, Out, Out, Out,Out, Out, Out, Out] 
      --prog = [Out, Add 1, Out, Add 0, Out, Clr, Out, Add 41, Out, Add 1, Out, Out, Out, Out]  
      --prog = [Add 1, Out, Out, Out, Out]  
      bin  = map encode prog
      initState = State { pc = 0, reg = 0, stalled = False, fetchInstruction = Add 0, writebackOut = (Nothing, Nothing)}

------------------------------------------------------------------------------------
-- Leakage Description and Proof
------------------------------------------------------------------------------------

-- {-# ANN tickRun UC
--   { observation = 'obs
--   , leakage = 'leak
--   , simulator = 'simRun
--   , projection = 'proj
--   } #-}

-- {-# ANN tickRun Spec
--   { observation' = 'obs
--   , leakage' = 'leak
--   , simulator' = 'simRun
--   , projection' = 'proj
--   } #-}

-- | Sim instructions
data LeakInst = LAdd Bool
                |  LOut 
                |  LClr
    deriving (Eq, Ord, Show) 

stateless :: (a -> b) -> Circuit () a b
stateless f _ i = ((), f i)

obs = stateless obs'

-- | Attacker can see whether there's an ouput + the PC.
obs' :: (Maybe Output, Word8) -> (Bool, Word8)
obs' (Just _, pc) = (True, pc)
obs' (_, pc) = (False, pc)

leakInst :: Instruction -> LeakInst
leakInst inst = case inst of
    Add imm -> LAdd $ imm==0
    Out     -> LOut
    Clr     -> LClr

-- | We leak the current instruction and whether it triggers the fast-path.
leak :: () -> Word16 -> ((), LeakInst)
leak _ rawInst = ((), leakInst inst)
    where
    inst = decode rawInst
        
-- | Simulation State
data LState = LState {
    lpc :: Word8,
    lstalled :: Bool,
    lFetchInst :: LeakInst,
    lWBout :: Bool
} deriving (Eq, Show)

simFetch :: MonadState LState m => LeakInst -> m ()
simFetch inst = do
    state <- get
    if lstalled state then return ()
    else do 
        put $ state {lFetchInst = inst, lpc = lpc state + 1}

simExec :: MonadState LState m => m ()
simExec = do
    state <- get
    let instr = lFetchInst state
    case instr of 
        -- fast path, execute now
        LAdd fast -> 
            if fast || lstalled state then do
                put state{lstalled = False, lWBout=False}
            else do
                put state{lstalled = True, lWBout=False}
        LOut ->
                put state{lstalled = False, lWBout=True}
        LClr ->
                put state{lstalled = False, lWBout=False}

simWB :: MonadState LState m => m (Bool, Word8)
simWB = do
    state <- get
    return (lWBout state, lpc state)

sim :: MonadState LState m => LeakInst -> m (Bool, Word8)
sim inst = do
    (out, pc) <- simWB
    simExec
    simFetch inst
    return (out, pc)

simRun :: LState -> LeakInst -> (LState, (Bool, Word8))
simRun s i = swap $ runState (sim i) s

proj :: (State, ()) -> ((), LState)
proj (s, _) = ((), ls)
    where    
    ls = LState{ 
          lpc = pc s 
        , lstalled = stalled s
        , lFetchInst = leakInst $ fetchInstruction s
        , lWBout = isJust $ snd $ writebackOut s
    }


-- lrun :: MonadState LState m => [Word16] -> m [Bool]
-- lrun program = do
--     state <- get
--     if lpc state >= fromIntegral (length program) 
--     then return []
--     else 
--         do
--         let inst = program !! fromIntegral (lpc state)
--         let (_, leaked) = leak () inst
--         (out, _) <- sim leaked
--         os <- lrun program
--         return $ out:os

-- ltest :: IO ()
-- ltest = do 
--     (os, s) <- runStateT (lrun bin) initState
--     putStrLn $ "halted, with final state" ++ show s
--     putStrLn $ "outputs" ++ show os
--     where 
--       --prog = [Out, Add 2, Out, Add 3, Out, Clr, Out]  
--       --prog = [Out, Add 2, Out, Clr, Out, Add 3, Out]  
--       prog = [Out, Add 1, Out, Add 0, Out, Clr, Out, Add 41, Out, Add 1, Out, Out, Out, Out,Out, Out, Out, Out] 
--       --prog = [Out, Add 1, Out, Add 0, Out, Clr, Out, Add 41, Out, Add 1, Out, Out, Out, Out]  
--       --prog = [Add 1, Out, Out, Out, Out]  
--       bin  = map encode prog
--       --initState = State { pc = 0, reg = 0, stalled = False, fetchInstruction = Add 0, writebackOut = (Nothing, Nothing)}
--       initState = LState {lpc =0, lstalled = False, lFetchInst = LAdd True, lWBout = False}

-- ------------------------------------------------------------------------------------
-- -- Correctness Theorem
-- ------------------------------------------------------------------------------------

-- -- instance Arbitrary Instruction where
-- --   arbitrary = oneof [
-- --     Add <$> arbitrary,
-- --     pure Clr,
-- --     pure Out
-- --     ]

-- -- theorem :: [Instruction] -> Bool
-- -- theorem prog = map isJust outs == outsL
-- --     where
-- --         bin = map encode prog
-- --         initState = State { pc = 0, reg = 0, stalled = False, fetchInstruction = Add 0, writebackOut = (Nothing, Nothing)}
-- --         initStateL = LState {lpc =0, lstalled = False, lFetchInst = LAdd True, lWBout = False}
-- --         (outs, _) = runState (run bin) initState
-- --         (outsL, _) = runState (lrun bin) initStateL
