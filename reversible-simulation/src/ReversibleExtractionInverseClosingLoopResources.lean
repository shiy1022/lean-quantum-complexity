import ReversibleExtractionInverseClosingLoopPolynomial

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Whole-prefix execution has a polynomial real instruction clock and polynomial exit counters. -/
theorem extractionInverseClosingLoopTemplate_resources (tm : Turing.FinTM2)
    (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat,(extractionInverseClosingLoopTemplate tm).PolynomiallyTimed bound ∧
      ∀ n (cs : ExtractionTraversalRegister → Nat),(∀ q,cs q ≤ bound.eval n) →
        ∀ q,(extractionInverseClosingLoopTemplate tm).counters cs q ≤ budget.eval n := by
  let D := 10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7
  let G := 41
  let stable := Polynomial.C 4*bound+Polynomial.C (D+3)
  let global := stable+bound+Polynomial.C G*bound
  refine ⟨global,extractionInverseClosingLoopTemplate_polynomial tm bound,?_⟩
  intro n cs hb q
  let B := bound.eval n
  let M := stable.eval n
  have hm : B ≤ M := by simp only [M,B,stable,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hsmall : 4*B+D+3 ≤ M := by simp only [M,B,stable,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]; omega
  have hloop : ∀ k spent (t : ExtractionTraversalRegister → Nat),
      ExtractionInverseClosingTraversalBudget tm B M spent t → spent+k ≤ B →
      ExtractionInverseClosingTraversalBudget tm B M (spent+k)
        (descendingTemplateCounters (extractionInverseClosingTraversalStepTemplate tm) 22 k t) := by
    intro k
    induction k with
    | zero => intro spent t hi hk; simpa only [descendingTemplateCounters,Nat.add_zero] using hi
    | succ k ih =>
      intro spent t hi hk
      let next := Function.update t (22 : ExtractionTraversalRegister) k
      have hn := extractionInverseClosingTraversalBudget_update tm B M spent k t hi (by omega)
      have hb' := extractionInverseClosingTraversalBudget_step tm B M spent next hn (by omega) hsmall
      have hj := ih (spent+1) ((extractionInverseClosingTraversalStepTemplate tm).counters next) hb' (by omega)
      simpa only [descendingTemplateCounters,next,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj
  have hi : ExtractionInverseClosingTraversalBudget tm B M (cs 22)
      (descendingTemplateCounters (extractionInverseClosingTraversalStepTemplate tm) 22 (cs 22) cs) := by
    simpa only [Nat.zero_add] using hloop (cs 22) 0 cs
      (extractionInverseClosingTraversalBudget_initial tm B M cs hb hm) (by simpa using hb 22)
  have hr := extractionInverseClosingTraversalBudget_update tm B M (cs 22) 0 _ hi (Nat.zero_le _)
  have hu := extractionInverseClosingTraversalBudget_uniform tm B M (cs 22) _ hr q
  have hl : G*(cs 22) ≤ G*B := Nat.mul_le_mul_left G (hb 22)
  simp only [global,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  change (extractionInverseClosingLoopTemplate tm).counters cs q ≤ M+B+G*B
  change (extractionInverseClosingLoopTemplate tm).counters cs q ≤ M+B+G*(cs 22) at hu
  omega

end ShiReversibleGenerator
