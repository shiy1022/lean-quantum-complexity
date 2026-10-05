import «AMPUNI-total-polynomial-clocked-machine»
import «AMPUNI-clocked-polynomial-interface»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2 Polynomial
noncomputable section
namespace ShiTMTotalPolynomialClocked
variable (tm : Turing.FinTM2) (inputEquiv : Bool ≃ tm.Γ tm.k₀)

/-- Every raw input terminates within a polynomial bound, including fuel
construction, source timeout, and canonical cleanup. -/
theorem total_polynomial (d k : Nat) :
    ∃ P : Polynomial ℕ, ∀ xs : List Bool, ∃ ys : List (tm.Γ tm.k₁),
      Nonempty (Turing.TM2OutputsInTime (finiteMachine tm inputEquiv d k)
        xs (some ys) (P.eval xs.length)) := by
  obtain ⟨Q, hQ⟩ := ShiTMClockedInterface.total_with_polynomial_budget tm
    (ShiTMPolynomialFuel.budgetPoly d k)
  refine ⟨ShiTMPolynomialFueledAssembly.prefixPoly d k + Q, ?_⟩
  intro xs
  obtain ⟨t, ys, hr, ht⟩ := hQ (xs.map inputEquiv)
  simp only [List.length_map, ShiTMPolynomialFuel.budgetPoly_eval] at hr ht
  have h := from_clocked_run tm inputEquiv d k xs ys t hr
  refine ⟨ys, ⟨{
    steps := ShiTMPolynomialFueledAssembly.prefixCost d k xs + t
    evals_in_steps := h
    steps_le_m := ?_ }⟩⟩
  simp only [eval_add, ShiTMPolynomialFueledAssembly.prefixPoly_eval]
  exact Nat.add_le_add_left ht _

/-- A valid source run within the monomial budget retains its output in
the complete total machine; the source's final state need not be canonical. -/
theorem valid_run_polynomial (d k : Nat) :
    ∃ P : Polynomial ℕ,
      ∀ (xs : List Bool) (steps : Nat) (v : tm.σ) (S : ∀ j, List (tm.Γ j)),
      (ShiTMSubroutine.run tm.m)^[steps]
        (some (Turing.initList tm (xs.map inputEquiv))) = some ⟨none, v, S⟩ →
      steps ≤ k * (xs.length + 1) ^ (d + 1) →
      Nonempty (Turing.TM2OutputsInTime (finiteMachine tm inputEquiv d k)
        xs (some (S tm.k₁)) (P.eval xs.length)) := by
  obtain ⟨Q, hQ⟩ := ShiTMClockedInterface.valid_run_with_polynomial_budget tm
    (ShiTMPolynomialFuel.budgetPoly d k)
  refine ⟨ShiTMPolynomialFueledAssembly.prefixPoly d k + Q, ?_⟩
  intro xs steps v S hr hb
  have hb' : steps ≤ (ShiTMPolynomialFuel.budgetPoly d k).eval
      (xs.map inputEquiv).length := by
    simpa only [List.length_map, ShiTMPolynomialFuel.budgetPoly_eval] using hb
  obtain ⟨t, ht, hcost⟩ := hQ (xs.map inputEquiv) steps v S hr hb'
  simp only [List.length_map, ShiTMPolynomialFuel.budgetPoly_eval] at ht hcost
  have h := from_clocked_run tm inputEquiv d k xs (S tm.k₁) t ht
  refine ⟨{
    steps := ShiTMPolynomialFueledAssembly.prefixCost d k xs + t
    evals_in_steps := h
    steps_le_m := ?_ }⟩
  simp only [eval_add, ShiTMPolynomialFueledAssembly.prefixPoly_eval]
  exact Nat.add_le_add_left hcost _

end ShiTMTotalPolynomialClocked
