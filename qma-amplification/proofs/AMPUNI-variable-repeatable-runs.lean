import «AMPUNI-repeat-fueled-bounds»
import «AMPUNI-variable-family»
import «AMPUNI-normalized-boolean-quadratic»

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ShiQMAVariableRounds
open ShiClassQMA ShiClassQMAU ShiClassQMAAmpX

/-- One fixed finite TM2 subroutine handles every valid iterated QMA encoding.
The subroutine stops at an active, clean output handoff for a following round. -/
theorem concrete_repeatable_round_runs :
    ∃ k C : Nat, ∀ (F : QMAFamily) (n r : Nat),
      let xs := ShiBQP.encNat n ++ encQMAFamilyAt (iter F r) n
      let ys := encQMAFamilyAt (ampFamilyX (iter F r)) n
      ∃ t : Nat,
        (ShiTMSubroutine.run
          (ShiTMRepeatFueled.finiteMachine
            ShiTMNormalizedEntry.booleanMachine
            (Equiv.refl Bool) k).m)^[t]
          (some (Turing.initList
            (ShiTMRepeatFueled.finiteMachine
              ShiTMNormalizedEntry.booleanMachine
              (Equiv.refl Bool) k) xs)) =
            some (ShiTMRepeatFueled.activeFinish
              ShiTMNormalizedEntry.booleanMachine
              (Equiv.refl Bool) k ys) ∧
        t ≤ C * (xs.length + 1) ^ 2 := by
  obtain ⟨k, hk⟩ := ShiTMNormalizedEntry.boolean_valid_input_quadratic
  obtain ⟨C, hC⟩ := ShiTMRepeatFueled.valid_quadratic
    ShiTMNormalizedEntry.booleanMachine (Equiv.refl Bool) k
  refine ⟨k, C, ?_⟩
  intro F n r
  let H := iter F r
  let xs := ShiBQP.encNat n ++ encQMAFamilyAt H n
  let ys := encQMAFamilyAt (ampFamilyX H) n
  have hv : Nonempty (Turing.TM2OutputsInTime
      ShiTMNormalizedEntry.booleanMachine
      (xs.map (Equiv.refl Bool)) (some ys)
      (k * (xs.length + 1) ^ 2)) := by
    have hv₀ : Nonempty (Turing.TM2OutputsInTime
        ShiTMNormalizedEntry.booleanMachine xs (some ys)
        (k * (xs.length + 1) ^ 2)) := by
      simpa [xs, ys, ShiTMRetainedPayload.inputLength] using (hk H n)
    have hmap : List.map (id : Bool → Bool) xs = xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [ih]
    change Nonempty (Turing.TM2OutputsInTime
      ShiTMNormalizedEntry.booleanMachine
      (List.map (id : Bool → Bool) xs) (some ys)
      (k * (xs.length + 1) ^ 2))
    exact hmap.symm ▸ hv₀
  obtain ⟨t, hr, ht⟩ := hC xs ys hv
  exact ⟨t, hr, ht⟩

end ShiQMAVariableRounds
