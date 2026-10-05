import «AMPUNI-layout-machine»
import Theorems.Thm_ShiTM_encNat_parser_block

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMLayoutMachine

/-- A one-index arm consumes exactly one unary operand from the retained source stack and
materializes its bare mark chain on layout stack 0. -/
theorem scan_one_operand
    (t : Fin 5) (ht : t.val < 4) (i : Nat) (rest : List Cell) (v : Sig)
    (S : ∀ k, List (Gam k))
    (hS : S 11 = (ShiBQP.encNat i).map bit ++ rest) :
    (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[i + 1]
        (some { l := some (operandLoopLabel t), var := v, stk := S }) =
      some ({
        l := some (operandFinishLabel t)
        var := pop (List.foldl (fun w y => pop w (some y)) v
          (List.replicate i (bit true))) (some (bit false))
        stk := Function.update (Function.update S 11 rest) 0
          (List.replicate i Cell.mark ++ S 0) } : Cfg Gam Label Sig)
    ∧ Nonempty (StateTransition.EvalsToInTime (step machine)
        { l := some (operandLoopLabel t), var := v, stk := S }
        (some ({
          l := some (operandFinishLabel t)
          var := pop (List.foldl (fun w y => pop w (some y)) v
            (List.replicate i (bit true))) (some (bit false))
          stk := Function.update (Function.update S 11 rest) 0
            (List.replicate i Cell.mark ++ S 0) } : Cfg Gam Label Sig))
        (i + 1))
    ∧ (Function.update (Function.update S 11 rest) 0
        (List.replicate i Cell.mark ++ S 0)) 11 = rest := by
  have h := ShiTM.encNat_parser_block machine
    (ka := (11 : Fin 14)) (kb := (0 : Fin 14)) (by decide)
    (lc := operandLoopLabel t) (lnext := operandFinishLabel t)
    (fpop := pop) (gtest := isMark) (hpush := cst .mark)
    (e := fun _ => .mark) bit (machine_readOperand t ht)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    i rest v S hS
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- The delimiter exit installs the layout tag above the terminal continuation token. -/
theorem finish_one_operand_to_wire
    (t : Fin 5) (ht : t.val < 4) (v : Sig) (S : ∀ k, List (Gam k)) :
    (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[1]
        (some { l := some (operandFinishLabel t), var := v, stk := S }) =
      some ({
        l := some (b .wire)
        var := v
        stk := Function.update S 7 (tagCell t :: .continueSingle :: S 7) } :
          Cfg Gam Label Sig) := by
  change some (stepAux (machine (operandFinishLabel t)) v S) = _
  rw [machine_operandFinish t ht]
  simp [finishOperand, stepAux, cst]

end ShiTMLayoutMachine
