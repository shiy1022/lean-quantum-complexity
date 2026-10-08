import ReversibleExtractionPaddedRegisterInjection
import ReversibleProgramTemplateListBudget

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Actual register injection retains polynomial exit bounds, including untouched ambient counters. -/
theorem extractionPaddedLift_budget (p : CounterProgramTemplate ExtractionTraversalRegister)
    (bound : Polynomial Nat) (hp : p.CounterBound bound) :
    (extractionPaddedLift p).CounterBound bound := by
  obtain ⟨budget,hbudget⟩ := hp
  refine ⟨budget+bound,?_⟩
  intro n cs hb q
  simp only [Polynomial.eval_add]
  by_cases hq : q.val < 24
  · let r : ExtractionTraversalRegister := ⟨q.val,hq⟩
    have he : extractionTraversalToPaddedRegister r=q := Fin.ext rfl
    have h := extractionPaddedLift_pull p cs r
    rw [he] at h
    rw [h]
    exact (hbudget n _ (fun z => hb _) r).trans (by omega)
  · rw [extractionPaddedLift_outside p cs q (by omega)]
    exact (hb q).trans (by omega)

end ShiReversibleGenerator
