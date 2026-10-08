import ReversibleExtractionForestRegisterInjection
import ReversibleProgramTemplateListBudget

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Actual register injection retains polynomial exit bounds, including untouched ambient counters. -/
theorem extractionForestLift_budget (p : CounterProgramTemplate ExtractionPaddedRegister)
    (bound : Polynomial Nat) (hp : p.CounterBound bound) :
    (extractionForestLift p).CounterBound bound := by
  obtain ⟨budget,hbudget⟩ := hp
  refine ⟨budget+bound,?_⟩
  intro n cs hb q
  simp only [Polynomial.eval_add]
  by_cases hq : q.val < 26
  · let r : ExtractionPaddedRegister := ⟨q.val,hq⟩
    have he : extractionPaddedToForestRegister r=q := Fin.ext rfl
    have h := extractionForestLift_pull p cs r
    rw [he] at h
    rw [h]
    exact (hbudget n _ (fun z => hb _) r).trans (by omega)
  · rw [extractionForestLift_outside p cs q (by omega)]
    exact (hb q).trans (by omega)

end ShiReversibleGenerator
