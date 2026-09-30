import «AMPUNI-layout-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMLayoutMachine

/-- The instruction dispatcher consumes the tag installed by the front-end parser. -/
theorem instruction_dispatch_step (t : Fin 5) (tail : List Cell)
    (v : Sig) (S : ∀ k, List (Gam k))
    (hS7 : S 7 = tagCell t :: tail) :
    (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[1]
      (some { l := some (b .instructionDispatch), var := v, stk := S }) =
        some ({
          l := some (instructionArmLabel (some (tagCell t)))
          var := some (tagCell t)
          stk := Function.update S 7 tail } : Cfg Gam Label Sig) := by
  change some (stepAux (machine (b .instructionDispatch)) v S) = _
  rw [show machine (b .instructionDispatch) =
    Stmt.pop 7 pop (Stmt.goto instructionArmLabel) from rfl]
  simp [stepAux, hS7, pop]

theorem instructionArmLabel_single (t : Fin 5) (ht : t.val < 4) :
    instructionArmLabel (some (tagCell t)) = operandLoopLabel t := by
  fin_cases t <;> simp_all [instructionArmLabel, tagCell, operandLoopLabel]

theorem instructionArmLabel_cnot :
    instructionArmLabel (some (tagCell (4 : Fin 5))) = b .readCnotFirst := by
  rfl

end ShiTMLayoutMachine
