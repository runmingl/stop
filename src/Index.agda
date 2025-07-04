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


-- Proof of equivalence between small-step and big-step semantics
import Equivalence.SmallStepBigStep     

-- Proof of equivalence between stack machine and big-step semantics
import Equivalence.StackMachineBigStep  

-- Proof of equivalence between small-step and big-stop semantics
import Equivalence.SmallStepBigStop

-- Proof of equivalence between big-step and big-stop semantics
import Equivalence.BigStepBigStop

-- Proof of equivalence between stack machine and big-stop semantics
import Equivalence.StackMachineBigStop  


-- Contains progress theorem stated in terms of Big-stop semantics (well-typed terms do not get stuck)
import Language.Progress                
