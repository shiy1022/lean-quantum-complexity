import «AMPUNI-total-clocked-machine»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
noncomputable section
namespace ShiTMTotalClocked
variable (tm : Turing.FinTM2) (inputEquiv : Bool ≃ tm.Γ tm.k₀)

/-- Every raw Boolean input has a canonical output within a uniform
quadratic bound, including fuel generation, transfer, clocking, and cleanup. -/
theorem total_quadratic (k : Nat) :
    ∃ C : Nat, ∀ xs : List Bool, ∃ ys : List (tm.Γ tm.k₁),
      Nonempty (Turing.TM2OutputsInTime (finiteMachine tm inputEquiv k) xs (some ys)
        (C*(xs.length+1)^2)) := by
  obtain ⟨D, hD⟩ := ShiTMClockedInterface.total_with_quadratic_budget tm k
  refine ⟨k+12+D, ?_⟩
  intro xs
  obtain ⟨t, ys, hr, ht⟩ := hD (xs.map inputEquiv)
  simp only [List.length_map] at hr ht
  have h := from_clocked_run tm inputEquiv k xs ys t hr
  have hp := ShiTMFueledAssembly.prefixCost_bound k xs
  refine ⟨ys, ⟨{
    steps := ShiTMFueledAssembly.prefixCost k xs+t
    evals_in_steps := h
    steps_le_m := ?_ }⟩⟩
  nlinarith

/-- Any source output certified within the budget is preserved by the
complete raw-input machine, with a uniform quadratic runtime. -/
theorem valid_quadratic (k : Nat) :
    ∃ C : Nat, ∀ (xs : List Bool) (ys : List (tm.Γ tm.k₁)),
      Nonempty (Turing.TM2OutputsInTime tm (xs.map inputEquiv) (some ys)
        (k*(xs.length+1)^2)) →
      Nonempty (Turing.TM2OutputsInTime (finiteMachine tm inputEquiv k) xs (some ys)
        (C*(xs.length+1)^2)) := by
  obtain ⟨D, hD⟩ := ShiTMClockedInterface.valid_with_quadratic_budget tm k
  refine ⟨k+12+D, ?_⟩
  intro xs ys hv
  have hv' : Nonempty (Turing.TM2OutputsInTime tm (xs.map inputEquiv) (some ys)
      (k*((xs.map inputEquiv).length+1)^2)) := by simpa only [List.length_map] using hv
  obtain ⟨t, hr, ht⟩ := hD (xs.map inputEquiv) ys hv'
  simp only [List.length_map] at hr ht
  have h := from_clocked_run tm inputEquiv k xs ys t hr
  have hp := ShiTMFueledAssembly.prefixCost_bound k xs
  refine ⟨{
    steps := ShiTMFueledAssembly.prefixCost k xs+t
    evals_in_steps := h
    steps_le_m := ?_ }⟩
  nlinarith

end ShiTMTotalClocked
