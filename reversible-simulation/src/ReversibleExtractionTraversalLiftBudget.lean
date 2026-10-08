import ReversibleExtractionTraversalRegisterInjection
import ReversibleProgramTemplateListBudget

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Actual register injection retains polynomial exit bounds, including untouched ambient counters. -/
theorem extractionTraversalLift_budget (p : CounterProgramTemplate ExtractionTermRegister)
    (bound : Polynomial Nat) (hp : p.CounterBound bound) :
    (extractionTraversalLift p).CounterBound bound := by
  obtain ⟨budget,hbudget⟩ := hp
  refine ⟨budget+bound,?_⟩
  intro n cs hb q
  simp only [Polynomial.eval_add]
  by_cases hq : q.val < 22
  · let r : ExtractionTermRegister := ⟨q.val,hq⟩
    have he : extractionTermToTraversalRegister r=q := Fin.ext rfl
    have h := extractionTraversalLift_pull p cs r
    rw [he] at h
    rw [h]
    exact (hbudget n _ (fun z => hb _) r).trans (by omega)
  · rw [extractionTraversalLift_outside p cs q (by omega)]
    exact (hb q).trans (by omega)

end ShiReversibleGenerator
