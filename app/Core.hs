{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wno-all #-}

module Core
(test) where

import GHC.Word (Word8 (..), Word16 (..), Word32 (..))
import GHC.Base (wordToWord8#, word8ToWord#, word16ToWord#, wordToWord16#, wordToWord32#)
import Data.Word
import Data.Bits


data Instr = Add Word8 | Clr | Out | Jmp Word8 | Beq Word8

data State = State { pc :: Word8 
                    , reg :: Word32 
                    , exInstr :: Instr 
                    , exPC :: Word8 
                    , wbOut :: (Maybe Word32 , Maybe Word32) }

fe :: State -> ( Word16 , Maybe Word8 ) -> (State, ())
fe state ( rawInstr , jmp ) =
    let curPC = pc state in
    let instr = decode rawInstr in
        case jmp of 
            Just newPC -> ( state { exInstr = Add 0 , exPC = curPC , pc = newPC }, ())
            Nothing -> ( state { exInstr = instr , exPC = curPC , pc = curPC + 1}, ())

ex :: State -> () -> (State , Maybe Word8)
ex state _ = 
    let curReg = reg state in
    case exInstr state of
        Add imm -> let newReg = curReg + word8ToWord32 imm in
            (state { wbOut = ( Just newReg , Nothing ) }, Nothing)
        Clr -> (state { wbOut = ( Just 0 , Nothing ) }, Nothing)
        Out -> (state { wbOut = ( Nothing , Just curReg) } , Nothing)
        Jmp addr -> ( state { wbOut = (Nothing , Nothing)}, Just addr)
        Beq off ->
            if curReg == 0 
            then let newPC = (exPC state) + off in
                ( state { wbOut = (Nothing , Nothing)}, Just newPC)
            else ( state { wbOut = (Nothing , Nothing)}, Nothing)

wb :: State -> () -> (State , Maybe Word32)
wb state _ =
    let (wb , out) = wbOut state in
        case wb of
            Just newReg -> (state {reg = newReg} , out)
            Nothing -> (state , out)

proc :: State -> Word16 -> ( State , ( Maybe Word32 , Word8 ))
proc state rawInstr =
    let ( state', out ) = wb state () in
    let ( state'', jmp ) = ex state' () in
    let ( state''', _ ) = fe state'' (rawInstr, jmp) in
        ( state''', (out, pc state'''))

test = putStrLn "Helno world!"

------------------------------------
-- | Modular leakage and simulator
------------------------------------

data LInstr = LJmp Word8 | LBeq Word8 | LOther

data LState = LState {lreg :: Word32, lexInstr :: Instr}

leak_ex :: LState -> (LState , (LInstr, Bool))
leak_ex state =
    let curReg = lreg state in
    case lexInstr state of
        Add imm -> let newReg = curReg + word8ToWord32 imm in 
            (state {lreg = newReg}, (LOther, False))
        Clr -> 
            (state {lreg = 0}, (LOther, False))
        Out -> 
            (state, (LOther, False))
        Jmp addr ->
            (state,  (LJmp addr, True))
        Beq off ->
            if curReg == 0
            then ( state, (LBeq off, True))
            else ( state, (LOther, False))   

sim_ex :: () -> LInstr -> ((), (Instr, Bool))
sim_ex _ lInst = 
    case lInst of
        LJmp addr ->
            ((), (Jmp addr, True))
        LBeq off ->
            ((), (Beq off, True))
        LOther ->
            ((), (Add 0, False))

leak_fe :: LState -> (Word16, Bool) ->  (LState , ())
leak_fe state (rawInstr, jmp) =
    let instr = decode rawInstr in
    if jmp 
    then  (state {lexInstr = instr}, ())
    else  (state {lexInstr = Add 0}, ())

sim_fe :: SState -> (Instr, Bool) -> (SState, Word8)
sim_fe state (instr, jmp) =
    let curPC = spc state in
    case instr of
        Jmp addr -> (state { sexPC = curPC , spc = addr }, addr)
        Beq off -> 
            if jmp
            then let newPC = (sexPC state) + off in
                 (state {sexPC = curPC , spc = newPC }, newPC)
            else (state { sexPC = curPC , spc = curPC + 1}, curPC + 1)
        _ -> (state { sexPC = curPC , spc = curPC + 1}, curPC + 1)

-----------------------------
-- | Monolithic Leakage
-----------------------------
leak :: LState -> Word16 -> ( LState , LInstr )
leak state rawInstr =
    let curReg = lreg state in
    let instr = decode rawInstr in
    case lexInstr state of
        Add imm -> let newReg = curReg + word8ToWord32 imm in 
            (state { lreg = newReg, lexInstr = instr}, LOther)
        Clr -> 
            (state { lreg = 0, lexInstr = instr}, LOther)
        Out -> 
            (state { lexInstr = instr}, LOther)
        Jmp addr ->
            (state { lexInstr = Add 0},  LJmp addr)
        Beq off ->
            if curReg == 0
            then ( state { lexInstr = Add 0} , LBeq off )
            else ( state { lexInstr = instr } , LOther )            


data SState = SState {spc :: Word8, sexPC :: Word8}

sim :: SState -> LInstr -> (SState, Word8)
sim state leakInstr =
    let curPC = spc state in
    case leakInstr of
        LOther -> (state { sexPC = curPC , spc = curPC + 1}, curPC + 1)
        LJmp addr -> (state { sexPC = curPC , spc = addr }, addr)
        LBeq off -> let newPC = ( sexPC state ) + off in
                    (state {sexPC = curPC , spc = newPC } , newPC)



-----------------------------
-- | Encoding and decoding
-----------------------------

word8ToWord16 :: Word8 -> Word16
word8ToWord16 (W8# value) = W16# $ wordToWord16# (word8ToWord# value)

word8ToWord32 :: Word8 -> Word32
word8ToWord32 (W8# value) = W32# $ wordToWord32# (word8ToWord# value)

word16ToWord8 :: Word16 -> Word8
word16ToWord8 (W16# value) = W8# $ wordToWord8# (word16ToWord# value)

encode :: Instr -> Word16
encode instruction = case instruction of
    Add value -> (0 `shiftL` 8) .|. word8ToWord16 value
    Clr       -> 1 `shiftL` 8
    Out       -> 2 `shiftL` 8
    Jmp addr    -> (3 `shiftL` 8) .|. word8ToWord16 addr
    Beq off   -> (4 `shiftL` 8) .|. word8ToWord16 off

decode :: Word16 -> Instr
decode word = case shiftR word 8 of
    0 -> Add (word16ToWord8 (word .&. 0xFF))
    1 -> Clr
    2 -> Out
    3 -> Jmp (word16ToWord8 (word .&. 0xFF))
    4 -> Beq (word16ToWord8 (word .&. 0xFF))
    _ -> Add 0
    --_ -> error "Invalid instruction"