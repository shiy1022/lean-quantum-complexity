import ReversibleExtractionInputSetupSourceBudget
import ReversibleExtractionForwardPrefixStepMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Actual whole-prefix bound addresses use only metadata that the retreat and negation frame. -/
theorem extractionForwardPrefixStepTemplate_source_address_budget (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, ∀ n (cs : ExtractionTermRegister → Nat),
      (∀ q ∈ ([0,1,2,11] : List ExtractionTermRegister),cs q ≤ bound.eval n) →
      ∀ q ∈ ([19,20,21] : List ExtractionTermRegister),
        (extractionForwardPrefixStepTemplate tm e stride).counters cs q ≤ budget.eval n := by
  obtain ⟨budget,h⟩ := extractionInputSetupTemplate_source_budget tm stride bound
  refine ⟨budget,?_⟩
  intro n cs hb q hq
  let t := (extractionForwardTermRetreatTemplate tm).counters cs
  let u := (extractionTermNegationPrinterTemplate false).counters t
  have ht : ∀ r ∈ ([0,1,2,11] : List ExtractionTermRegister),t r=cs r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals exact (extractionForwardTermRetreatTemplate_frame tm cs _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hu : ∀ r ∈ ([0,1,2,11] : List ExtractionTermRegister),u r=t r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    all_goals exact (extractionTermNegationPrinterTemplate_frame false t _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have metadata : ∀ r ∈ ([0,1,2,11] : List ExtractionTermRegister),u r ≤ bound.eval n := by
    intro r hr
    rw [hu r hr,ht r hr]
    exact hb r hr
  have ha := h n u metadata q hq
  have hq2 : q ≠ 2 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  change (decrementProgramTemplate (2 : ExtractionTermRegister)).counters
    ((extractionBoundTermPrinterTemplate tm e stride false).counters u) q ≤ budget.eval n
  simp only [decrementProgramTemplate,Function.update_of_ne hq2]
  change (extractionTermDispatchTemplate tm e false (extractionBoundInputs tm stride)).counters
    ((extractionInputSetupTemplate tm stride).counters u) q ≤ budget.eval n
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl
  all_goals rw [extractionTermDispatchTemplate_frame tm e false (extractionBoundInputs tm stride) _ _
    (by decide) (by decide) (by decide) (by decide) (by decide)]
  all_goals exact ha

end ShiReversibleGenerator
