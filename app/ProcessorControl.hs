{-# LANGUAGE FlexibleContexts #-}

module ProcessorControl
    ( test
    , check
    , tickRun
    , obs
    , leakRun
    , simRun
    , proj
    ) where
--import Test.QuickCheck

import Data.Word
import Data.Bits
import Control.Monad.State (MonadState, MonadIO, put, get, runStateT, runState, liftIO)
import Data.Maybe (isJust)
import Data.Tuple (swap)
import Projection
import UC
import Test.QuickCheck hiding ((.&.))
import Debug.Trace

data Instruction = Add Word8
                -- ^ Add immediate to the register
                |  Clr
                -- ^ Reset the register to zero
                |  Out 
                -- ^ Output the register value
                | J Word8        
                -- ^ Jump to target address
                | Beq Word8      
                -- ^ Branch if register equals zero to PC + offset
                deriving (Eq, Ord, Show) 

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
-- 11 - J (with 8-bit target address)
-- 100 - Beq (with 8-bit offset)

encode :: Instruction -> Word16
encode instruction = case instruction of
    Add value -> (0 `shiftL` 8) .|. fromIntegral value
    Clr       -> 1 `shiftL` 8
    Out       -> 2 `shiftL` 8
    J addr    -> (3 `shiftL` 8) .|. fromIntegral addr
    Beq off   -> (4 `shiftL` 8) .|. fromIntegral off

decode :: Word16 -> Instruction
decode word = case shiftR word 8 of
    0 -> Add (fromIntegral (word .&. 0xFF))
    1 -> Clr
    2 -> Out
    3 -> J (fromIntegral (word .&. 0xFF))
    4 -> Beq (fromIntegral (word .&. 0xFF))
    _ -> error "Invalid instruction"

testEncoding :: IO ()
testEncoding = do
    let testInsts = [Add 42, Clr, Out, J 10, Beq 5]
    let results = map (\inst -> decode (encode inst) == inst) testInsts
    putStrLn $ "Encode/decode tests passed: " ++ show (and results)
    putStrLn $ "Individual results: " ++ show (zip testInsts results)

data State = State {
    -- architectural state
    pc :: Word8,
    reg :: Word32,
    -- instruction should be ignored
    bubble :: Bool,
    -- needed for jumps
    nextPc :: Word8,
    -- pipeline registers
    fetchPC :: Word8,
    fetchInstruction :: Instruction,
    writebackOut :: (Maybe Writeback, Maybe Output)
} deriving (Eq, Show)

-- Helper types remain the same
newtype Output = Val Word32 deriving (Eq, Show)
newtype Writeback = Write Word32 deriving (Eq, Show)

-- -- | Pipeline Stages
fetch :: MonadState State m => Word16 -> m Word8
fetch rawInstr = do
    state <- get
    let inst = if bubble state 
               then Add 0  -- No-op
               else decode rawInstr
    put $ state {
        fetchInstruction = inst,
        fetchPC = pc state,
        pc = nextPc state ,
        bubble = False  
        -- ^ Clear bubble flag after using it
    }
    return $ nextPc state 

execute :: MonadState State m => m ()
execute = do 
    state <- get
    let inst = fetchInstruction state
    case inst of
        Add value -> 
            let result = reg state + fromIntegral value in
            put $ state {writebackOut = (Just $ Write result, Nothing), nextPc = pc state + 1}
        Clr ->
            put $ state {writebackOut = (Just (Write 0), Nothing), nextPc = pc state + 1}
        Out ->
            put $ state {writebackOut = (Nothing, Just $ Val (reg state)), nextPc = pc state + 1}
        J addr ->
            put $ state {
                writebackOut = (Nothing, Nothing),
                bubble = True,
                nextPc = addr  
                -- ^ Mark next instruction as invalid
            }
        Beq offset ->
            if reg state == 0 
            then put $ state {
                writebackOut = (Nothing, Nothing),
                bubble = True,  
                -- ^ Mark next instruction as invalid
                nextPc = fetchPC state + offset
            }
            else put $ state {writebackOut = (Nothing, Nothing), nextPc = pc state + 1}

writeback :: MonadState State m => m (Maybe Output)
writeback = do
   state <- get
   let (wb, out) = writebackOut state
   -- Update register if there's a writeback
   put state{
       reg = maybe (reg state) (\(Write v) -> v) wb
   }
   return out

tick :: MonadState State m => Word16 -> m (Maybe Output, Word8)
tick rawInst = do
   --(out, pc) <- writeback
   out <- writeback
   execute 
   pc <- fetch rawInst
   return (out, pc)

tickRun :: State -> Word16 -> (State, (Maybe Output, Word8))
tickRun s i = swap $ runState (tick i) s    

genInstruction :: Int -> Gen Instruction
genInstruction len = frequency [
    (2, Add <$> arbitrary),     -- More weight on Add as it's common
    (1, pure Clr),              -- Simple instructions
    (1, pure Out),
    (2, J <$> choose (0, fromIntegral len - 1)),  -- Jump within bounds
    (2, Beq <$> choose (0, fromIntegral len - 1)) -- Branch within bounds
  ]

genProgram :: Gen [Instruction]
genProgram = do
    len <- choose (1, 20)
    sequence $ replicate len (genInstruction len)

-- instance Arbitrary [Instruction] where
--     arbitrary = genProgram

test :: IO ()
test = do
    putStrLn "Test 1: Jump"
    runAndShow run prog initState
    putStrLn "Simulator output"
    runAndShow lrun prog (linit, sinit)
   --sample (genProgram)
   --putStrLn $ "program: " ++ (show (sample (genProgram)))

   --putStrLn "\nTest 2: Sequential with Add"
   --runAndShow prog2
 where
   maxSteps = 50
   prog = [Out, Add 228, J 8, Add 11, Clr, Clr, Add 53, J 2, Beq 0, Out, Clr, Out, Out, Add 190, Beq 5, J 9, Add 155]
   prog1 = [Out, J 3, Add 5, Add 10, Out, Out, Out, Out]  -- Should output 0, 10, 10
   prog2 = [Add 1, Out, Clr, Out, Beq 2, Out, Add 2, Out, Out, Out, Out]  -- Should output 1, 1, 3

   (linit, sinit) = proj initState

   runAndShow runF prog init = do
       (outs, s) <- runStateT (runF maxSteps $ map encode prog) init
       putStrLn $ "State: " ++ show s
       putStrLn $ "Outputs: " ++ show outs

initState = State { 
       pc = 0, 
       nextPc = 1,
       reg = 0, 
       bubble = False,
       fetchInstruction = Add 0,
       writebackOut = (Nothing, Nothing)
   }

run :: MonadState State m => Int -> [Word16] -> m [Word8]
run maxSteps program = go maxSteps
  where
    go steps = do
      state <- get
      if steps <= 0
      then return []  -- Terminate if max steps reached
      else if pc state >= fromIntegral (length program)
      then return []  -- Terminate if program complete
      else do
        let inst = program !! fromIntegral (pc state)
        (out, pc) <- tick inst
        os <- go (steps - 1)  -- Decrement remaining steps
        return $ pc:os
------------------------------------------------------------------------------------
-- Leakage Description and Proof
------------------------------------------------------------------------------------

{-# ANN tickRun UC
  { observation = 'obs
  , leakage = 'leakRun
  , simulator = 'simRun
  , projection = 'proj
  } #-}

-- | Instructions passed to the Simulator
data LeakInst = LBeq Bool Word8
-- ^ are we taking the branch + offset
            | LJ Word8
-- ^ jump target                
            | LOther 
-- ^ all other instructions
    deriving (Eq, Ord, Show) 

-- | Attacker can only see the PC.
obs :: (Maybe Output, Word8) -> (Word8)
obs (_, pc) =  pc

-- from instruction (and register value) to leakage instruction
leakInst :: Instruction -> Word32 -> LeakInst
leakInst (J addr) _ =  LJ addr
leakInst (Beq offset) reg = LBeq (reg==0) offset
leakInst _ _ = LOther

-- | Projection from state to leakage and simulator state
proj :: State -> (LeakState, SimState)
proj state = (leakState, simState)
    where
    leakState = LState {lreg = reg state, lbubble = bubble state}
    simState = SimState {simPc = pc state, simBubble = bubble state, simNextPc = nextPc state, simFetchPc= fetchPC state, simFetchInstruction = leakInst (fetchInstruction state) (reg state)}

-- | Leakage Description State
data LeakState = LState {
    lreg :: Word32,
    lbubble :: Bool
} deriving (Eq, Show)

leak :: MonadState LeakState m => Word16 -> m LeakInst
-- ^ Leak needs to keep track of the register state to know whether to branch or not.
leak rawInst = do
    lstate <- get
    let inst = if lbubble lstate 
               then Add 0  -- No-op
               else decode rawInst
    put $ lstate {lbubble = False}
    lstate <- get
    -- ^ state updates and instruction
    case inst of 
        Add value -> do
            let result = lreg lstate + fromIntegral value
            put $ lstate {lreg = result}
            return LOther
        Clr -> do
            put $ lstate {lreg = 0}
            return LOther
        J addr -> do
            put $ lstate {lbubble = True}
            return $ LJ addr
        Beq offset ->
            if lreg lstate == 0 
            then do 
                put $ lstate {lbubble = True}
                return $ LBeq True offset
            else return $ LBeq False offset
        Out -> return LOther

    -- ^ returning leakage instruction 
    --let lInst = leakInst inst (lreg lstate)
    --return lInst
    --trace ("inst: " ++ (show inst) ++ " leak inst: " ++ show lInst) $ return lInst

leakRun :: LeakState -> Word16 -> (LeakState, LeakInst)
leakRun s i = swap $ runState (leak i) s    

-- | Simulation State
data SimState = SimState {
    simPc :: Word8,
    simBubble :: Bool,
    simNextPc :: Word8,
    simFetchPc :: Word8,
    simFetchInstruction :: LeakInst
} deriving (Eq, Show)

-- | Pipeline Stages -- simulator
simFetch :: MonadState SimState m => LeakInst -> m Word8
simFetch inst0 = do
    state <- get
    let inst = if simBubble state 
               then LOther  -- No-op
               else inst0
    put $ state {
        simFetchInstruction = inst,
        simFetchPc = simPc state,
        simPc = simNextPc state,
        simBubble = False
    }
    return $ simNextPc state 


simExecute :: MonadState SimState m => m ()
simExecute = do 
    state <- get
    let inst = simFetchInstruction state
    case inst of
        LOther -> 
            put $ state {simNextPc = simPc state + 1}
        LJ addr ->
            put $ state {
                simNextPc = addr,
                simBubble = True
            }
        LBeq taken offset ->
            if taken 
            then put $ state {
                simNextPc = simFetchPc state + offset,
                simBubble = True
            }
            else put $ state {simNextPc = simPc state + 1}    

-- ^ We don't need writeback.
simTick :: MonadState SimState m => LeakInst -> m Word8
simTick inst = do
   simExecute 
   pc <- simFetch inst
   return pc

simRun :: SimState -> LeakInst -> (SimState, Word8)
simRun s i = swap $ runState (simTick i) s    

lTick :: MonadState (LeakState, SimState) m => Word16 -> m Word8
lTick inst = do
    (leaks, sims) <- get
    let (leaks', lInst) = leakRun leaks inst
    let (sims', out) = simRun sims lInst
    put $ (leaks', sims')
    return out


lrun :: MonadState (LeakState, SimState) m => Int -> [Word16] -> m [Word8]
lrun maxSteps program = go maxSteps
  where
    go steps = do
      (leakState, simState) <- get
      if steps <= 0
      then return []  -- Terminate if max steps reached
      else if simPc simState >= fromIntegral (length program)
      then return []  -- Terminate if program complete
      else do
        let inst = program !! fromIntegral (simPc simState)
        out <- lTick inst
        os <- go (steps - 1)  -- Decrement remaining steps
        return $ out:os

-- | Correctness Theorem
theorem :: [Instruction] -> Bool
theorem prog = outI == outS
    where
    maxSteps = 100
    (outI, _) = runState (run maxSteps $ map encode prog) initState
    (outS, _) = runState (lrun maxSteps $ map encode prog) simInit
    simInit = proj initState

prop_theorem :: Property
prop_theorem = forAll genProgram theorem

check = quickCheckWith stdArgs{maxSuccess = 5000000} prop_theorem 

