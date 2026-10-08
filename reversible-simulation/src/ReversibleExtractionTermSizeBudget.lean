import ReversibleExtractionTermSizeResources

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

theorem extractionSizeContribution_bound (tm : Turing.FinTM2) (ell j : Nat) :
    extractionSizeContribution tm ell j ≤ 10+Fintype.card (Option (MachineSymbol tm))*7 := by
  unfold extractionSizeContribution
  split_ifs <;> omega

/-- Runtime term-size computation bounds all its real exit counters, including the cached doubled length. -/
theorem extractionTermSizeProgramTemplate_budget (tm : Turing.FinTM2) (bound : Polynomial Nat)
    (n : Nat) (cs : ExtractionTermRegister → Nat) (hb : ∀ q,cs q ≤ bound.eval n) :
    ∀ q,(extractionTermSizeProgramTemplate tm).counters cs q ≤
      (Polynomial.C 2*bound+Polynomial.C (10+Fintype.card (Option (MachineSymbol tm))*7)).eval n := by
  intro q
  rw [extractionTermSizeProgramTemplate_counters]
  have hc := extractionSizeContribution_bound tm (cs 2) (cs 1)
  have h2 := hb 2
  have hq := cleanupCounters_uniform_bound [12,5,6,7] cs (bound.eval n) hb q
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  by_cases h12 : q=12
  · subst q; simp only [Function.update_self]; omega
  · rw [Function.update_of_ne h12]
    by_cases h3 : q=3
    · subst q; simp only [Function.update_self]; omega
    · rw [Function.update_of_ne h3]
      omega

end ShiReversibleGenerator
