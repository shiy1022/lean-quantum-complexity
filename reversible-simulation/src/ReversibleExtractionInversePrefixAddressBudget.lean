import ReversibleExtractionInversePrefixStepReady
import ReversibleExtractionInputSetupSourceBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The surviving current-empty-marker address depends only on stable input metadata and length. -/
theorem extractionInversePrefixStepTemplate_source_address_budget (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat,∀ n (cs : ExtractionTermRegister → Nat),
      (∀ q ∈ ([0,1,2,11] : List ExtractionTermRegister),cs q ≤ bound.eval n) →
      (extractionInversePrefixStepTemplate tm e stride).counters cs 20 ≤ budget.eval n := by
  obtain ⟨budget,h⟩ := extractionInputSetupTemplate_source_budget tm stride bound
  refine ⟨budget,?_⟩
  intro n cs hb
  let t := (extractionTermSizeProgramTemplate tm).counters cs
  let u := (extractionBoundTermPrinterTemplate tm e stride true).counters t
  let v := (extractionTermNegationPrinterTemplate true).counters u
  have ht : ∀ q ∈ ([0,1,2,11] : List ExtractionTermRegister),t q ≤ bound.eval n := by
    intro q hq
    have hq' := hb q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals simpa [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply] using hq'
  have ha := h n t ht 20 (by simp)
  change extractionPrefixAdvanceTemplate.counters v 20 ≤ _
  simp only [extractionPrefixAdvanceTemplate_counters,
    Function.update_of_ne (by decide : (20 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (20 : ExtractionTermRegister) ≠ 18),
    Function.update_of_ne (by decide : (20 : ExtractionTermRegister) ≠ 8)]
  change (extractionTermNegationPrinterTemplate true).counters u 20 ≤ _
  rw [extractionTermNegationPrinterTemplate_frame true u 20
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  change (extractionTermDispatchTemplate tm e true (extractionBoundInputs tm stride)).counters
    ((extractionInputSetupTemplate tm stride).counters t) 20 ≤ _
  rw [extractionTermDispatchTemplate_frame tm e true (extractionBoundInputs tm stride) _ 20
    (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact ha

end ShiReversibleGenerator
