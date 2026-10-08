import ReversibleExtractionForwardClosingLoopPolynomial

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The actual closing traversal has both a polynomial clock and polynomial exit counters. -/
theorem extractionForwardClosingLoopTemplate_resources (tm : Turing.FinTM2) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat,(extractionForwardClosingLoopTemplate tm).PolynomiallyTimed bound ∧
      ∀ n (cs : ExtractionTermRegister → Nat),(∀ q,cs q ≤ bound.eval n) →
        ∀ q,(extractionForwardClosingLoopTemplate tm).counters cs q ≤ budget.eval n := by
  let budget := Polynomial.C 2*bound+
    Polynomial.C (extractionClosingContributionBudget tm+45)*(bound+Polynomial.C 1)
  refine ⟨budget,extractionForwardClosingLoopTemplate_polynomial tm bound,?_⟩
  intro n cs hb q
  let B := bound.eval n
  have hloop : ∀ k spent (t : ExtractionTermRegister → Nat),
      ExtractionClosingLoopBudget tm B spent t → spent+k ≤ B →
      ExtractionClosingLoopBudget tm B (spent+k)
        (descendingTemplateCounters (extractionClosingStepTemplate tm false) 9 k t) := by
    intro k
    induction k with
    | zero => intro spent t hi hk; simpa only [descendingTemplateCounters,Nat.add_zero] using hi
    | succ k ih =>
      intro spent t hi hk
      let next := Function.update t (9 : ExtractionTermRegister) k
      have hn := extractionClosingLoopBudget_update tm B spent k t hi (by omega)
      have ha := extractionClosingLoopBudget_step tm false B spent next hn
      have hj := ih (spent+1) ((extractionClosingStepTemplate tm false).counters next) ha (by omega)
      simpa only [descendingTemplateCounters,next,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj
  have hi : ExtractionClosingLoopBudget tm B (cs 9)
      (descendingTemplateCounters (extractionClosingStepTemplate tm false) 9 (cs 9) cs) := by
    simpa only [Nat.zero_add] using hloop (cs 9) 0 cs
      (extractionClosingLoopBudget_initial tm B cs hb) (by simpa using hb 9)
  have hr := extractionClosingLoopBudget_update tm B (cs 9) 0 _ hi (Nat.zero_le _)
  have hg := extractionClosingLoopBudget_global tm B (cs 9) _ hr (hb 9) q
  simpa only [extractionForwardClosingLoopTemplate,descendingProgramTemplate,budget,B,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] using hg

end ShiReversibleGenerator
