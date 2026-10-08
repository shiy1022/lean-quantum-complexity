import ReversibleTickHeaderInvariants

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickHeaderTemplate_polynomial (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool)
    (bound : Polynomial Nat) : (tickHeaderTemplate tm inputStride strideBound backward).PolynomiallyTimed bound := by
  apply sequenceProgramTemplate_polynomial _ _ bound bound
  · exact cleanupProgramTemplate_polynomial _ bound
  · intro n cs hb _
    exact cleanupCounters_uniform_bound [.inl 2] cs (bound.eval n) hb
  · exact (tickCoordinateListTemplate_polynomial_certificate tm _ inputStride strideBound backward bound).2

/-- Header execution has an actual polynomial clock under the separate static and layer budgets. -/
theorem tickHeaderTemplate_clock (tm : Turing.FinTM2) (inputStride strideBound : Nat) (backward : Bool)
    (budget layers : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat),
      fixedGuardedEmitterReady (tickTraversalSupply tm) cs → CounterBudget cs (.inl 9) (budget.eval n) →
      cs (.inl 9) ≤ layers.eval n →
      (tickHeaderTemplate tm inputStride strideBound backward).steps cs ≤ clock.eval n := by
  obtain ⟨clock,hclock⟩ := tickHeaderTemplate_polynomial tm inputStride strideBound backward (budget+layers)
  refine ⟨clock,?_⟩
  intro n cs hr hb hl
  apply hclock n cs _ (tickHeaderTemplate_ready tm inputStride strideBound backward cs hr)
  intro q
  rw [Polynomial.eval_add]
  by_cases hq : q=Sum.inl 9
  · subst q; exact hl.trans (Nat.le_add_left _ _)
  · exact (hb q hq).trans (Nat.le_add_right _ _)

end ShiReversibleGenerator
