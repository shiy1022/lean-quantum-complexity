import ReversibleExtractionCleanForestLoop
import ReversibleExtractionCleanForestBudgetStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- One fixed polynomial bounds the whole actual loop, with no iteration of counter-bound polynomials. -/
theorem extractionCleanForestLoopTemplate_polynomial (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (extractionCleanForestLoopTemplate tm e stride backward).PolynomiallyTimed bound := by
  let D := 10+Fintype.card (Option (MachineSymbol tm))*7
  let layers := Polynomial.C 37*(Polynomial.C 1+(bound+Polynomial.C 1)*Polynomial.C D)+Polynomial.C 1
  let global := bound+bound*(layers+bound+Polynomial.C 2)
  obtain ⟨clock,hclock⟩ := (extractionCleanForestStepTemplate_resources tm e stride backward global).2
  refine ⟨(Polynomial.C 2+clock)*bound+Polynomial.C 1,?_⟩
  intro n cs hb hr
  let B := bound.eval n
  have hg : global.eval n=B+B*(extractionForestLayerIncrementBound tm B+B+2) := by
    simp [global,layers,B,D,extractionForestLayerIncrementBound,extractionBitBound]
  have hloop : ∀ k spent (t : ExtractionForestRegister → Nat),
      ExtractionCleanForestBudget tm B spent t → spent+k ≤ B →
      descendingTemplateReady (extractionCleanForestStepTemplate tm e stride backward) 26 k t →
      descendingTemplateSteps (extractionCleanForestStepTemplate tm e stride backward) 26 k t ≤
        (2+clock.eval n)*k+1 := by
    intro k
    induction k with
    | zero => intro spent t hi hk hready; simp [descendingTemplateSteps]
    | succ k ih =>
      intro spent t hi hk hready
      let next := Function.update t (26 : ExtractionForestRegister) k
      let after := (extractionCleanForestStepTemplate tm e stride backward).counters next
      have hn := extractionCleanForestBudget_update tm B spent k t hi (by omega)
      have hu : ∀ q,next q ≤ global.eval n := by
        rw [hg]
        exact extractionCleanForestBudget_uniform tm B spent next hn (by omega)
      have ht := hclock n next hu hready.1
      have ha := extractionCleanForestBudget_step tm e stride backward B spent next hn
      have hj := ih (spent+1) after ha (by omega) hready.2.2
      rw [descendingTemplateSteps]
      change 2+(extractionCleanForestStepTemplate tm e stride backward).steps next+
        descendingTemplateSteps (extractionCleanForestStepTemplate tm e stride backward) 26 k after ≤ _
      simp only [Nat.mul_succ]
      omega
  have hs := hloop (cs 26) 0 cs (extractionCleanForestBudget_initial tm B cs hb)
    (by simpa using hb 26) hr
  have hh := Nat.add_le_add_right (Nat.mul_le_mul_left (2+clock.eval n) (hb 26)) 1
  simpa only [extractionCleanForestLoopTemplate,descendingProgramTemplate,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C] using hs.trans hh

end ShiReversibleGenerator
