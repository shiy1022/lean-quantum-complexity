import ReversibleExtractionInverseClosingTraversalBudget
import ReversibleExtractionInverseClosingStepPolynomial

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- One fixed polynomial state budget bounds the real entire prefix loop, including every loop instruction. -/
theorem extractionInverseClosingLoopTemplate_polynomial (tm : Turing.FinTM2)
    (bound : Polynomial Nat) :
    (extractionInverseClosingLoopTemplate tm).PolynomiallyTimed bound := by
  let D := 10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7
  let G := 41
  let stable := Polynomial.C 4*bound+Polynomial.C (D+3)
  let global := stable+bound+Polynomial.C G*bound
  have body := extractionTraversalLift_polynomial (extractionInverseClosingStepTemplate tm) global
    (extractionInverseClosingStepTemplate_polynomial tm global)
  obtain ⟨clock,hclock⟩ := body
  refine ⟨(Polynomial.C 2+clock)*bound+Polynomial.C 1,?_⟩
  intro n cs hb hr
  let B := bound.eval n
  let M := stable.eval n
  have hm : B ≤ M := by simp only [M,B,stable,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hsmall : 4*B+D+3 ≤ M := by simp only [M,B,stable,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hloop : ∀ k spent (t : ExtractionTraversalRegister → Nat),
      ExtractionInverseClosingTraversalBudget tm B M spent t → spent+k ≤ B →
      descendingTemplateReady (extractionInverseClosingTraversalStepTemplate tm) 22 k t →
      descendingTemplateSteps (extractionInverseClosingTraversalStepTemplate tm) 22 k t ≤
        (2+clock.eval n)*k+1 := by
    intro k
    induction k with
    | zero => intro spent t hi hk hready; simp [descendingTemplateSteps]
    | succ k ih =>
      intro spent t hi hk hready
      let next := Function.update t (22 : ExtractionTraversalRegister) k
      let after := (extractionInverseClosingTraversalStepTemplate tm).counters next
      have hn := extractionInverseClosingTraversalBudget_update tm B M spent k t hi (by omega)
      have hg : ∀ q,next q ≤ global.eval n := by
        intro q
        have hu := extractionInverseClosingTraversalBudget_uniform tm B M spent next hn q
        have hs : spent ≤ B := by omega
        have hl := Nat.mul_le_mul_left G hs
        simp only [global,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
        change next q ≤ M+B+G*B
        change next q ≤ M+B+G*spent at hu
        omega
      have ht := hclock n next hg hready.1
      change (extractionInverseClosingTraversalStepTemplate tm).steps next ≤ clock.eval n at ht
      have hb' := extractionInverseClosingTraversalBudget_step tm B M spent next hn (by omega) hsmall
      have hj := ih (spent+1) after hb' (by omega) hready.2.2
      rw [descendingTemplateSteps]
      change 2+(extractionInverseClosingTraversalStepTemplate tm).steps next+
        descendingTemplateSteps (extractionInverseClosingTraversalStepTemplate tm) 22 k after ≤ _
      simp only [Nat.mul_succ]
      omega
  have hs := hloop (cs 22) 0 cs (extractionInverseClosingTraversalBudget_initial tm B M cs hb hm)
    (by simpa using hb 22) hr
  have hm' := Nat.add_le_add_right (Nat.mul_le_mul_left (2+clock.eval n) (hb 22)) 1
  simpa only [extractionInverseClosingLoopTemplate,descendingProgramTemplate,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C] using hs.trans hm'

end ShiReversibleGenerator
