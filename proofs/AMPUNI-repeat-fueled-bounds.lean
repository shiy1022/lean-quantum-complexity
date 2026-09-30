import «AMPUNI-repeat-fueled-machine»
import «AMPUNI-repeat-clocked-bounds»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
noncomputable section

namespace ShiTMRepeatFueled
variable (tm : Turing.FinTM2) (inputEquiv : Bool ≃ tm.Γ tm.k₀)

/-- A successful source output reaches the active handoff in quadratic time
from an ordinary raw Boolean input, including fuel construction. -/
theorem valid_quadratic (k : Nat) :
    ∃ C : Nat, ∀ (xs : List Bool) (ys : List (tm.Γ tm.k₁)),
      Nonempty (Turing.TM2OutputsInTime tm (xs.map inputEquiv)
        (some ys) (k * (xs.length + 1) ^ 2)) →
      ∃ t : Nat,
        (ShiTMSubroutine.run (finiteMachine tm inputEquiv k).m)^[t]
          (some (Turing.initList (finiteMachine tm inputEquiv k) xs)) =
            some (activeFinish tm inputEquiv k ys) ∧
        t ≤ C * (xs.length + 1) ^ 2 := by
  obtain ⟨D, hD⟩ :=
    ShiTMRepeatClockedInterface.valid_with_quadratic_budget tm k
  refine ⟨k + 12 + D, ?_⟩
  intro xs ys hv
  have hv' : Nonempty (Turing.TM2OutputsInTime tm
      (xs.map inputEquiv) (some ys)
      (k * ((xs.map inputEquiv).length + 1) ^ 2)) := by
    simpa only [List.length_map] using hv
  obtain ⟨t, hr, ht⟩ := hD (xs.map inputEquiv) ys hv'
  simp only [List.length_map] at hr ht
  have h := from_clocked_run tm inputEquiv k xs ys t hr
  have hp := ShiTMFueledAssembly.prefixCost_bound k xs
  refine ⟨ShiTMFueledAssembly.prefixCost k xs + t, h, ?_⟩
  nlinarith

end ShiTMRepeatFueled
