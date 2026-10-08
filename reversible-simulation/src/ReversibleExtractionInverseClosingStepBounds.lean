import ReversibleExtractionInverseClosingStepMetadata
import ReversibleExtractionClosingStepFieldBound
import ReversibleExtractionClosingStepScratchMetadata

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Extra unchanged index sources and the emptied retreat scratch do not grow across inverse closing. -/
theorem extractionInverseClosingStepTemplate_extra_frame (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) (q : ExtractionTermRegister)
    (hq : q ∈ ([4,9,10] : List ExtractionTermRegister)) :
    (extractionInverseClosingStepTemplate tm).counters cs q=cs q := by
  let t := (extractionInverseClosingRetreatTemplate tm).counters cs
  let u := (extractionBoundClosingPrinterTemplate tm true).counters t
  have ht : t q=cs q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact (extractionInverseClosingRetreatTemplate_frame tm cs _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hu : u q=t q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact (extractionBoundClosingPrinterTemplate_frame tm true t _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide))
  have he : extractionInverseClosingAdvanceTemplate.counters u q=u q := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals simp [extractionInverseClosingAdvanceTemplate_counters]
  exact he.trans (hu.trans ht)

/-- Every overwritten scratch or field has a source-dependent bound, independent of its old value. -/
theorem extractionInverseClosingStepTemplate_overwritten (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) (B E : Nat) (h2 : cs 2 ≤ B) (h18 : cs 18 ≤ E) (h20 : cs 20 ≤ E) :
    let after := (extractionInverseClosingStepTemplate tm).counters cs
    let D := 10+Fintype.card (Option (MachineSymbol tm))*7
    after 3 ≤ 2*B ∧ after 5=0 ∧ after 6=0 ∧ after 7=0 ∧ after 8=0 ∧ after 12 ≤ D ∧
      after 13 ≤ E+D+3 ∧ after 14 ≤ E+D+3 ∧ after 15 ≤ E+D+3 ∧
      after 19 ≤ E+D ∧ after 21 ≤ E := by
  let t := (extractionInverseClosingRetreatTemplate tm).counters cs
  let u := (extractionBoundClosingPrinterTemplate tm true).counters t
  have ht2 : t 2=cs 2 := extractionInverseClosingRetreatTemplate_frame tm cs 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have ht18 : t 18 ≤ E := by
    change (extractionInverseClosingRetreatTemplate tm).counters cs 18 ≤ E
    rw [extractionInverseClosingRetreatTemplate_base]
    omega
  have ht20 : t 20 ≤ E := (extractionInverseClosingRetreatTemplate_frame tm cs 20
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans_le h20
  have ht8 : t 8=0 := by simp [t,extractionInverseClosingRetreatTemplate_counters]
  have hu8 : u 8=0 := (extractionBoundClosingPrinterTemplate_frame tm true t 8
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht8
  have hc := extractionBoundClosingPrinterTemplate_cache tm true t
  have hd := extractionSizeContribution_bound tm (t 2) (t 1)
  have hf := extractionBoundClosingPrinterTemplate_fields_bound tm true t E ht18 ht20
  have hp : u 19=t 18+extractionSizeContribution tm (t 2) (t 1)-4 ∧ u 21=t 20-3 := by
    have hx : ∀ q ∈ ([19,21] : List ExtractionTermRegister),u q=(extractionClosingSetupTemplate tm).counters t q := by
      intro q hq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl
      all_goals exact (fixedNodeCounters_other extractionTermNodeRegisters _ _ (by decide) (by decide) (by decide) (by decide) _)
    simp [hx 19 (by simp),hx 21 (by simp),extractionClosingSetupTemplate_counters]
  change extractionInverseClosingAdvanceTemplate.counters u 3 ≤ 2*B ∧
    extractionInverseClosingAdvanceTemplate.counters u 5=0 ∧
    extractionInverseClosingAdvanceTemplate.counters u 6=0 ∧
    extractionInverseClosingAdvanceTemplate.counters u 7=0 ∧
    extractionInverseClosingAdvanceTemplate.counters u 8=0 ∧
    extractionInverseClosingAdvanceTemplate.counters u 12 ≤ _ ∧
    extractionInverseClosingAdvanceTemplate.counters u 13 ≤ _ ∧
    extractionInverseClosingAdvanceTemplate.counters u 14 ≤ _ ∧
    extractionInverseClosingAdvanceTemplate.counters u 15 ≤ _ ∧
    extractionInverseClosingAdvanceTemplate.counters u 19 ≤ _ ∧
    extractionInverseClosingAdvanceTemplate.counters u 21 ≤ E
  have ha3 : extractionInverseClosingAdvanceTemplate.counters u 3=u 3 := by
    simp [extractionInverseClosingAdvanceTemplate_counters]
  have ha : ∀ q ∈ ([5,6,7,8,12,13,14,15,19,21] : List ExtractionTermRegister),
      extractionInverseClosingAdvanceTemplate.counters u q=u q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [extractionInverseClosingAdvanceTemplate_counters]
  simp only [ha3,ha 5 (by simp),ha 6 (by simp),ha 7 (by simp),ha 8 (by simp),ha 12 (by simp),
    ha 13 (by simp),ha 14 (by simp),ha 15 (by simp),ha 19 (by simp),ha 21 (by simp)]
  dsimp only at hc hf
  change u 3=2*t 2 ∧ u 5=0 ∧ u 6=0 ∧ u 7=0 ∧ u 12=extractionSizeContribution tm (t 2) (t 1) at hc
  change u 13 ≤ _ ∧ u 14 ≤ _ ∧ u 15 ≤ _ at hf
  rcases hc with ⟨hc3,hc5,hc6,hc7,hc12⟩
  rcases hf with ⟨hf13,hf14,hf15⟩
  rcases hp with ⟨hp19,hp21⟩
  rw [ht2] at hc3
  omega

end ShiReversibleGenerator
