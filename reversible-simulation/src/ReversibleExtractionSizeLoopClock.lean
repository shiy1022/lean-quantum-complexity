import ReversibleExtractionSizeStepClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Count every guard, arithmetic instruction, loop test and decrement in the actual size pass. -/
theorem extractionSizeLoopTemplate_polynomial (tm : Turing.FinTM2) (bound : Polynomial Nat) :
    (extractionSizeLoopTemplate tm).PolynomiallyTimed bound := by
  have h : ∀ k (cs : ExtractionSizeRegister → Nat) B,
      CounterBudget cs 4 (2*B) → (extractionSizeStepTemplate tm).ready cs → k ≤ B →
      descendingTemplateSteps (extractionSizeStepTemplate tm) 2 k cs ≤
        k*(200*B+102+Fintype.card (Option (MachineSymbol tm))*7)+1 := by
    intro k
    induction k with
    | zero => intro cs B hb hr hk; simp [descendingTemplateSteps]
    | succ k ih =>
      intro cs B hb hr hk
      have hu := hb.update (2 : ExtractionSizeRegister) k (by omega : k ≤ 2*B)
      obtain ⟨h5,h6,h7⟩ := (extractionSizeStepTemplate_ready tm cs).1 hr
      have hur : (extractionSizeStepTemplate tm).ready (Function.update cs 2 k) := by
        rw [extractionSizeStepTemplate_ready]
        simpa using And.intro h5 (And.intro h6 h7)
      have hcost := extractionSizeStepTemplate_cost_bound tm (Function.update cs 2 k) (2*B) hu hur
      have hn := extractionSizeStepTemplate_counter_budget tm (Function.update cs 2 k) B hu (by simpa using (show k ≤ B by omega))
      have hnr := extractionSizeStepTemplate_ready_preserved tm (Function.update cs 2 k) hur
      have hnext := ih ((extractionSizeStepTemplate tm).counters (Function.update cs 2 k)) B hn hnr (by omega)
      rw [descendingTemplateSteps,Nat.succ_mul]
      omega
  refine ⟨bound*(Polynomial.C 200*bound+Polynomial.C (102+Fintype.card (Option (MachineSymbol tm))*7))+Polynomial.C 1,?_⟩
  intro n cs hb hr
  by_cases hzero : cs 2=0
  · simp only [extractionSizeLoopTemplate,descendingProgramTemplate,hzero,descendingTemplateSteps,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hzero
  have hs : (extractionSizeStepTemplate tm).ready cs := by
    change descendingTemplateReady (extractionSizeStepTemplate tm) 2 (cs 2) cs at hr
    rw [hk] at hr
    have hu := hr.1
    rw [extractionSizeStepTemplate_ready] at hu ⊢
    simpa using hu
  have hh := h (cs 2) cs (bound.eval n) (by intro q hq; have hq' := hb q; omega) hs (hb 2)
  have hm := Nat.mul_le_mul_right (200*bound.eval n+102+Fintype.card (Option (MachineSymbol tm))*7) (hb 2)
  simp only [extractionSizeLoopTemplate,descendingProgramTemplate,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Nat.add_assoc] at hh hm ⊢
  omega

end ShiReversibleGenerator
