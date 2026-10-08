import ReversibleExtractionClosingLoopBudgetStep
import ReversibleExtractionClosingLoopBudgetUpdate
import ReversibleExtractionClosingStepPolynomial
import ReversibleExtractionForwardClosingLoop

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- A single global state budget bounds the actual closing traversal clock, including every loop instruction. -/
theorem extractionForwardClosingLoopTemplate_polynomial (tm : Turing.FinTM2) (bound : Polynomial Nat) :
    (extractionForwardClosingLoopTemplate tm).PolynomiallyTimed bound := by
  let global := Polynomial.C 2*bound+
    Polynomial.C (extractionClosingContributionBudget tm+45)*(bound+Polynomial.C 1)
  obtain ⟨clock,hclock⟩ := extractionClosingStepTemplate_polynomial tm false global
  refine ⟨(Polynomial.C 2+clock)*bound+Polynomial.C 1,?_⟩
  intro n cs hb hr
  let B := bound.eval n
  have hloop : ∀ k spent (t : ExtractionTermRegister → Nat),
      ExtractionClosingLoopBudget tm B spent t → spent+k ≤ B →
      descendingTemplateReady (extractionClosingStepTemplate tm false) 9 k t →
      descendingTemplateSteps (extractionClosingStepTemplate tm false) 9 k t ≤
        (2+clock.eval n)*k+1 := by
    intro k
    induction k with
    | zero => intro spent t hi hk hready; simp [descendingTemplateSteps]
    | succ k ih =>
      intro spent t hi hk hready
      let next := Function.update t (9 : ExtractionTermRegister) k
      let after := (extractionClosingStepTemplate tm false).counters next
      have hn := extractionClosingLoopBudget_update tm B spent k t hi (by omega)
      have hg : ∀ q,next q ≤ global.eval n := by
        intro q
        simpa only [global,B,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] using
          extractionClosingLoopBudget_global tm B spent next hn (by omega) q
      have ht := hclock n next hg hready.1
      have ha := extractionClosingLoopBudget_step tm false B spent next hn
      have hj := ih (spent+1) after ha (by omega) hready.2.2
      rw [descendingTemplateSteps]
      change 2+(extractionClosingStepTemplate tm false).steps next+
        descendingTemplateSteps (extractionClosingStepTemplate tm false) 9 k after ≤ _
      simp only [Nat.mul_succ]
      omega
  have hs := hloop (cs 9) 0 cs (extractionClosingLoopBudget_initial tm B cs hb) (by simpa using hb 9) hr
  have hm := Nat.add_le_add_right (Nat.mul_le_mul_left (2+clock.eval n) (hb 9)) 1
  simpa only [extractionForwardClosingLoopTemplate,descendingProgramTemplate,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C] using hs.trans hm

end ShiReversibleGenerator
