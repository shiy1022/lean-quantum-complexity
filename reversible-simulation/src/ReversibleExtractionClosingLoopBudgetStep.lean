import ReversibleExtractionClosingLoopBudgetData
import ReversibleExtractionClosingStepFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionClosingLoopBudget_step (tm : Turing.FinTM2) (backward : Bool) (B spent : Nat)
    (cs : ExtractionTermRegister → Nat) (h : ExtractionClosingLoopBudget tm B spent cs) :
    ExtractionClosingLoopBudget tm B (spent+1) ((extractionClosingStepTemplate tm backward).counters cs) := by
  let after := (extractionClosingStepTemplate tm backward).counters cs
  have hm := extractionClosingStepTemplate_metadata tm backward cs
  have hx := extractionClosingStepTemplate_cache tm backward cs
  have hd := extractionSizeContribution_bound tm (cs 2) (cs 1)
  change extractionSizeContribution tm (cs 2) (cs 1) ≤ extractionClosingContributionBudget tm at hd
  have hf := extractionClosingStepTemplate_fields_bound tm backward cs
    (B+extractionClosingContributionBudget tm*spent) h.base (by have := h.endpoint; omega)
  change after 13 ≤ B+extractionClosingContributionBudget tm*spent+extractionClosingContributionBudget tm+3 ∧
    after 14 ≤ B+extractionClosingContributionBudget tm*spent+extractionClosingContributionBudget tm+3 ∧
    after 15 ≤ B+extractionClosingContributionBudget tm*spent+extractionClosingContributionBudget tm+3 at hf
  rcases hx with ⟨hx3,hx5,hx6,hx7,hx12⟩
  rcases hf with ⟨hf13,hf14,hf15⟩
  have ht : after 19=after 18 ∧ after 21=after 20 := by
    simp [after,extractionClosingStepTemplate,sequenceProgramTemplate,extractionClosingAdvanceTemplate_counters]
  have hbase : after 18 ≤ B+extractionClosingContributionBudget tm*(spent+1) := by
    have hb := h.base
    have he := hm.2.1
    change after 18=cs 18+extractionSizeContribution tm (cs 2) (cs 1)-3 at he
    rw [Nat.mul_succ]
    omega
  have hend : after 20 ≤ B := by
    have hb := h.endpoint
    have he := hm.2.2
    change after 20=cs 20-3 at he
    omega
  refine {
    length := ?_
    base := hbase
    endpoint := hend
    count := ?_
    stable := ?_
    cache := ?_
    size := ?_
    fields := ?_
    termPointer := ht.1.trans_le hbase
    suffixPointer := ht.2.trans_le hend
    scratch := ?_ }
  · have hb := h.length
    have he := hm.1
    change after 2=cs 2+1 at he
    omega
  · change after 16 ≤ B+41*(spent+1)
    have hb := h.count
    have he := extractionClosingStepTemplate_count tm backward cs
    change after 16=cs 16+41 at he
    omega
  · intro q hq
    have hn := hq
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hn
    rcases hn with ⟨h2,h3,h5,h6,h7,h12,h13,h14,h15,h16,h18,h19,h20,h21⟩
    exact (extractionClosingStepTemplate_frame tm backward cs q h2 h3 h5 h6 h7 h12 h13 h14 h15 h16 h18 h19 h20 h21).trans_le (h.stable q hq)
  · have hb := h.length
    have he := hx3
    change after 3=2*cs 2 at he
    omega
  · have he := hx12
    change after 12=extractionSizeContribution tm (cs 2) (cs 1) at he
    omega
  · intro q hq
    change after q ≤ B+extractionClosingContributionBudget tm*(spent+1)+extractionClosingContributionBudget tm+3
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals simp only [Nat.mul_succ]
    all_goals omega
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals omega

end ShiReversibleGenerator
