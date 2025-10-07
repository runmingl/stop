module Index where

-- Defines the syntax and type system of the PCF language
import Language.PCF


-- Small-step operational semantics for PCF
import Language.SmallStep               

-- Big-step (natural) semantics for PCF
import Language.BigStep                

-- An abstract stack machine semantics for PCF
import Language.StackMachine            

-- Big-stop semantics for PCF 
import Language.BigStop      


-- Proof of soundness and completeness between small-step and big-step semantics
import SoundnessCompleteness.SmallStepBigStep     

-- Proof of soundness and completeness between stack machine and big-step semantics
import SoundnessCompleteness.StackMachineBigStep  

-- Proof of soundness and completeness between stack machine and small-step semantics
import SoundnessCompleteness.StackMachineSmallStep

-- Proof of soundness and completeness between small-step and big-stop semantics
import SoundnessCompleteness.SmallStepBigStop

-- Proof of soundness and completeness between big-step and big-stop semantics
import SoundnessCompleteness.BigStepBigStop

-- Proof of soundness and completeness between stack machine and big-stop semantics
import SoundnessCompleteness.StackMachineBigStop  


-- Contains progress theorem stated in terms of Big-stop semantics (well-typed terms do not get stuck)
import Language.Progress                
