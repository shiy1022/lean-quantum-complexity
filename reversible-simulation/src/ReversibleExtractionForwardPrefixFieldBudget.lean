import ReversibleExtractionBoundTermFieldBudget
import ReversibleExtractionForwardPrefixStepMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The whole prefix body resets all printer fields using bounded stable metadata alone. -/
theorem extractionForwardPrefixStepTemplate_source_fields_budget (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, ∀ n (cs : ExtractionTermRegister → Nat),
      (∀ q ∈ ([0,1,2,11,18] : List ExtractionTermRegister),cs q ≤ bound.eval n) →
      ∀ q ∈ ([13,14,15] : List ExtractionTermRegister),
        (extractionForwardPrefixStepTemplate tm e stride).counters cs q ≤ budget.eval n := by
  obtain ⟨budget,h⟩ := extractionBoundTermPrinterTemplate_source_fields_budget tm e stride false bound
  refine ⟨budget,?_⟩
  intro n cs hb q hq
  let t := (extractionForwardTermRetreatTemplate tm).counters cs
  let u := (extractionTermNegationPrinterTemplate false).counters t
  have ht : ∀ r ∈ ([0,1,2,11,18] : List ExtractionTermRegister),t r ≤ bound.eval n := by
    intro r hr
    have hbr := hb r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact (extractionForwardTermRetreatTemplate_frame tm cs _
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans_le hbr
      | exact (extractionForwardTermRetreatTemplate_base tm cs).trans_le ((Nat.sub_le _ _).trans hbr)
  have hu : ∀ r ∈ ([0,1,2,11,18] : List ExtractionTermRegister),u r ≤ bound.eval n := by
    intro r hr
    have htr := ht r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals exact (extractionTermNegationPrinterTemplate_frame false t _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans_le htr
  have hf := h n u hu q hq
  have hq2 : q ≠ 2 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl <;> decide
  simpa only [extractionForwardPrefixStepTemplate,sequenceProgramTemplate,decrementProgramTemplate,
    Function.update_of_ne hq2] using hf

end ShiReversibleGenerator
