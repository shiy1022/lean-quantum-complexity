import «AMPUNI-layout-machine»
import «AMPUNI-emit-reverse-compose»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMLayoutMachine

/-- Consume either terminal continuation token and enter the common reversal loop in one
machine step. -/
theorem done_to_reverse
    (terminal : Cell)
    (hterminal : terminal = .continueSingle ∨ terminal = .continueCnotEnd)
    (v : Sig) (S : ∀ k, List (Gam k)) (tail : List Cell)
    (hS7 : S 7 = terminal :: tail) :
    (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[1]
        (some { l := some (b .done), var := v, stk := S }) =
      some ({
        l := some (b .reverseOutput)
        var := pop v (some terminal)
        stk := Function.update S 7 tail } : Cfg Gam Label Sig) := by
  change some (stepAux (machine (b .done)) v S) = _
  rw [show machine (b .done) = Stmt.pop 7 pop (Stmt.goto continuationLabel) from rfl]
  rcases hterminal with rfl | rfl <;>
    simp only [stepAux, hS7, List.head?_cons, List.tail_cons, pop, continuationLabel]

/-- Specialization of the accepted transfer block: stack 6 is drained and its chunk is
reversed onto the persistent accumulator stack 13. -/
theorem reverse_chunk_into_accumulator
    (q : Nat) (start : Cfg Gam Label Sig) (vmid : Sig)
    (S T : ∀ k, List (Gam k)) (chunk : List Cell)
    (hemit :
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[q] (some start) =
        some { l := some (b .reverseOutput), var := vmid, stk := T })
    (htmp : T 6 = chunk) :
    ∃ (vout : Sig) (U : ∀ k, List (Gam k)),
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[q + (chunk.length + 1)]
          (some start) = some { l := some (b .instructionDone), var := vout, stk := U }
      ∧ U 13 = chunk.reverse ++ T 13
      ∧ U 6 = []
      ∧ (∀ k, k ≠ 6 → k ≠ 13 → U k = T k)
      ∧ Nonempty (StateTransition.EvalsToInTime (step machine)
          start (some { l := some (b .instructionDone), var := vout, stk := U })
          (q + (chunk.length + 1))) := by
  simpa using
    (ShiTMEmitReverseCompose.emit_then_reverse_into_accumulator machine
      (ktmp := (6 : Fin 14)) (kacc := (13 : Fin 14)) (by decide)
      (lemit := start.l.getD (b .halt)) (lrev := b .reverseOutput)
      (lnext := b .instructionDone) (fpop := pop) (gtest := isSome)
      (hpush := get) (e := id) q start vmid S T chunk hemit htmp rfl
      (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl))

end ShiTMLayoutMachine
