import ReversibleTickLateWindowFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Runtime pointer seeding and both finite subtraction loops have a polynomial instruction clock. -/
theorem tickLateWindowTemplate_polynomial (tm : Turing.FinTM2) (bound : Nat)
    (budget : Polynomial Nat) : (tickLateWindowTemplate tm bound).PolynomiallyTimed budget := by
  let nextBudget := budget+Polynomial.C bound
  change (sequenceProgramTemplate _ _).PolynomiallyTimed budget
  apply sequenceProgramTemplate_polynomial _ _ budget nextBudget
  · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ budget
  · intro n cs hb _ q
    change Function.update cs (.inl 0) (1*cs (tickTraversalSpare tm 1)+bound-0) q ≤ nextBudget.eval n
    simp only [nextBudget,Polynomial.eval_add,Polynomial.eval_C,Nat.one_mul,Nat.sub_zero]
    by_cases hq : q=Sum.inl 0
    · subst q; rw [Function.update_self]; exact Nat.add_le_add_right (hb _) bound
    · rw [Function.update_of_ne hq]; exact (hb q).trans (Nat.le_add_right _ _)
  · apply sequenceProgramTemplate_polynomial _ _ nextBudget nextBudget
    · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ nextBudget
    · intro n cs hb _ q
      change Function.update cs (tickTraversalSpare tm 2) (1*cs (tickTraversalSpare tm 1)+0-0) q ≤ nextBudget.eval n
      simp only [Nat.one_mul,Nat.add_zero,Nat.sub_zero]
      by_cases hq : q=tickTraversalSpare tm 2
      · subst q; rw [Function.update_self]; exact hb _
      · rw [Function.update_of_ne hq]; exact hb q
    · apply sequenceProgramTemplate_polynomial _ _ nextBudget nextBudget
      · exact tickWindowRetreatTemplate_polynomial tm bound nextBudget
      · intro n cs hb _ q
        rw [tickWindowRetreatTemplate_counters]
        have h0 := hb (.inl 0)
        have h2 := hb (tickTraversalSpare tm 2)
        have hq := hb q
        simp only [Function.update_apply]
        split_ifs <;> omega
      · exact tickInputRetreatTemplate_polynomial tm bound nextBudget

end ShiReversibleGenerator
