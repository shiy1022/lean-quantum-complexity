import «AMPUNI-clocked-cleanup-interface»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2 Polynomial
noncomputable section
namespace ShiTMClockedInterface
variable (tm : Turing.FinTM2)
local instance polynomialStacksFinite : Fintype tm.K := tm.kFin
local instance polynomialLabelsFinite : Fintype tm.Λ := tm.ΛFin

/-- A supplied polynomial fuel budget bounds all inputs, including malformed
ones, with a polynomial cost for clocking and canonical cleanup. -/
theorem total_with_polynomial_budget (P : Polynomial ℕ) :
    ∃ Q : Polynomial ℕ, ∀ xs : List (tm.Γ tm.k₀),
      ∃ (t : Nat) (ys : List (tm.Γ tm.k₁)),
        (run tm)^[t] (some (start tm (P.eval xs.length) xs)) =
          some (finish tm ys) ∧ t ≤ Q.eval xs.length := by
  obtain ⟨c, h⟩ := total_with_budget tm
  let a := Fintype.card (ShiTMTypedTimeout.ClockK tm.K)
  let Q : Polynomial ℕ := C (c + 1) * (C 2 * P + 1) + X + P + C (a + 2)
  refine ⟨Q, ?_⟩
  intro xs
  obtain ⟨t, ys, hr, ht⟩ := h (P.eval xs.length) xs
  refine ⟨t, ys, hr, ?_⟩
  simpa [Q, a, Nat.add_assoc] using ht

/-- A sufficiently large supplied polynomial budget preserves a successful
source run even when its final finite state differs from the initial state. -/
theorem valid_run_with_polynomial_budget (P : Polynomial ℕ) :
    ∃ Q : Polynomial ℕ,
      ∀ (xs : List (tm.Γ tm.k₀)) (steps : Nat) (v : tm.σ)
        (S : ∀ j, List (tm.Γ j)),
      (ShiTMSubroutine.run tm.m)^[steps] (some (Turing.initList tm xs)) =
        some ⟨none, v, S⟩ →
      steps ≤ P.eval xs.length →
      ∃ t : Nat,
        (run tm)^[t] (some (start tm (P.eval xs.length) xs)) =
          some (finish tm (S tm.k₁)) ∧ t ≤ Q.eval xs.length := by
  obtain ⟨c, h⟩ := ShiTMClockedCleanup.preserves_bounded_run tm.k₁ tm.initialState tm.m
  let a := Fintype.card (ShiTMTypedTimeout.ClockK tm.K)
  let Q : Polynomial ℕ := C (c + 3) * P + X + C (a + 2)
  refine ⟨Q, ?_⟩
  intro xs steps v S hr hb
  obtain ⟨t, ht, hcost⟩ := h (P.eval xs.length) steps (Turing.initList tm xs) v S hr hb
  refine ⟨t, ht, ?_⟩
  rw [initial_size] at hcost
  simpa [Q, a, Nat.add_assoc] using hcost

end ShiTMClockedInterface
