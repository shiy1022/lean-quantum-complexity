import ReversibleExtractionInputBindingSourceBudget
import ReversibleExtractionInputSetupAgreement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Concrete setup addresses are bounded by stable capacity, output index, length and input base alone. -/
theorem extractionInputSetupTemplate_source_budget (tm : Turing.FinTM2) (stride : Nat)
    (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, ∀ n (cs : ExtractionTermRegister → Nat),
      (∀ q ∈ ([0,1,2,11] : List ExtractionTermRegister),cs q ≤ bound.eval n) →
      ∀ q ∈ ([19,20,21] : List ExtractionTermRegister),
        (extractionInputSetupTemplate tm stride).counters cs q ≤ budget.eval n := by
  obtain ⟨budget,h⟩ := extractionInputBindingTemplate_source_budget tm stride bound
  refine ⟨budget,?_⟩
  intro n cs hb q hq
  let indexed := (cleanupProgramTemplate [8]).counters
    (extractionIndexSetupTemplate.counters ((cleanupProgramTemplate [7,8]).counters cs))
  have h0 : indexed 0=cs 0 := by
    simp [indexed,cleanupProgramTemplate,cleanupCounters_apply,extractionIndexSetupTemplate_counters]
  have h2 : indexed 2=cs 2 := by
    simp [indexed,cleanupProgramTemplate,cleanupCounters_apply,extractionIndexSetupTemplate_counters]
  have h11 : indexed 11=cs 11 := by
    simp [indexed,cleanupProgramTemplate,cleanupCounters_apply,extractionIndexSetupTemplate_counters]
  have h4 : indexed 4=cs 1-cs 2-1 := by
    simp [indexed,cleanupProgramTemplate,cleanupCounters_apply,extractionIndexSetupTemplate_counters]
  have h10 : indexed 10=cs 2-1 := by
    simp [indexed,cleanupProgramTemplate,cleanupCounters_apply,extractionIndexSetupTemplate_counters]
  have indexedBound : ∀ r ∈ ([0,2,4,10,11] : List ExtractionTermRegister),indexed r ≤ bound.eval n := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    have hb0 := hb 0 (by simp)
    have hb1 := hb 1 (by simp)
    have hb2 := hb 2 (by simp)
    have hb11 := hb 11 (by simp)
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals simp only [h0,h2,h4,h10,h11]
    all_goals omega
  simpa only [extractionInputSetupTemplate,sequenceProgramTemplate,indexed] using h n indexed indexedBound q hq

end ShiReversibleGenerator
