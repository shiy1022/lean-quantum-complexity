import «AMPUNI-layout-machine»
import «AMPUNI-instruction-front»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMLayoutMachine

def tagOfNat (q : Nat) : Cell :=
  if h : q < 5 then tagCell ⟨q, h⟩ else .tag0

/-- Exact front-end run of the unified machine on a valid source instruction tag.  Stack 11
retains the unparsed operand suffix, stack 7 receives the finite dispatch token, and the
temporary unary counter on stack 12 is empty again. -/
theorem concrete_instruction_front
    (c : Nat) (hc : c < 5) (z : List Bool) (rest : List Cell) (u : Sig)
    (S : ∀ k, List (Gam k))
    (hSin : S 11 = List.map bit (ShiBQP.encNat c ++ z) ++ rest)
    (hScount : S 12 = []) :
    ∃ (v : Sig) (T : ∀ k, List (Gam k)),
      (fun cf : Option (Cfg Gam Label Sig) => cf.bind (step machine))^[c + 1 + (c + 1)]
        (some { l := some (b .parseTag), var := u, stk := S }) =
          some { l := some (b .instructionDispatch), var := v, stk := T }
      ∧ T 11 = List.map bit z ++ rest
      ∧ T 7 = tagCell ⟨c, hc⟩ :: S 7
      ∧ T 12 = []
      ∧ (∀ k, k ≠ 11 → k ≠ 12 → k ≠ 7 → T k = S k)
      ∧ Nonempty (StateTransition.EvalsToInTime (step machine)
          { l := some (b .parseTag), var := u, stk := S }
          (some { l := some (b .instructionDispatch), var := v, stk := T })
          (c + 1 + (c + 1))) := by
  obtain ⟨v, T, hrun, hTin, hTtag, hTcount, hframe⟩ :=
    ShiTMInstructionFront.parse_tag_to_dispatch machine
      (kin := (11 : Fin 14)) (kmark := (12 : Fin 14)) (ktag := (7 : Fin 14))
      (by decide) (by decide) (by decide)
      (.mark) bit tagOfNat 5
      (lb := b .parseTag) (ldisp := b .instructionDispatch) (lcnt := countLabel)
      (fpopI := pop) (gtestI := isMark) (hpushM := cst .mark)
      (eIM := fun _ => .mark) (fpopM := pop) (gmark := isSome)
      rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl
      (fun q hq => by simpa [tagOfNat, hq] using machine_count q hq)
      (fun _ => rfl) (fun _ => rfl)
      c hc z rest u S hSin hScount
  have htag : tagOfNat c = tagCell ⟨c, hc⟩ := by simp [tagOfNat, hc]
  rw [htag] at hTtag
  refine ⟨v, T, hrun, hTin, hTtag, hTcount, hframe, ?_⟩
  exact ⟨⟨⟨c + 1 + (c + 1), hrun⟩, le_rfl⟩⟩

end ShiTMLayoutMachine
