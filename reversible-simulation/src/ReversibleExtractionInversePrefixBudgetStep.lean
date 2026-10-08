import ReversibleExtractionInversePrefixBudgetData
import ReversibleExtractionInversePrefixScratchMetadata
import ReversibleExtractionInversePrefixPointerMetadata
import ReversibleExtractionTermSizeBudget

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator

/-- Actual inverse-body scratch remains bounded while length, base and count grow separately. -/
theorem extractionInversePrefixStepTemplate_other_budget (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride B M spent : Nat) (cs : ExtractionTermRegister → Nat)
    (h : ExtractionInversePrefixBudget tm e B M spent cs) (hs : spent ≤ B)
    (hsmall : 4*B+(1+(10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7))*B+
      (10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7)+1 ≤ M)
    (hf : ∀ q ∈ ([13,14,15] : List ExtractionTermRegister),
      (extractionInversePrefixStepTemplate tm e stride).counters cs q ≤ M)
    (ha : (extractionInversePrefixStepTemplate tm e stride).counters cs 20 ≤ M) :
    ∀ q,q ≠ 2 → q ≠ 18 → q ≠ 16 →
      (extractionInversePrefixStepTemplate tm e stride).counters cs q ≤ M := by
  let after := (extractionInversePrefixStepTemplate tm e stride).counters cs
  have hb0 := h.source 0 (by simp)
  have hb1 := h.source 1 (by simp)
  have hb11 := h.source 11 (by simp)
  have hb17 := h.source 17 (by simp)
  have hb2 := h.length
  have hb18 := (extractionInversePrefixBudget_sources tm e B M spent cs h hs).2
  have h0 : after 0=cs 0 := extractionInversePrefixStepTemplate_source_frame tm e stride cs 0 (by simp)
  have h1 : after 1=cs 1 := extractionInversePrefixStepTemplate_source_frame tm e stride cs 1 (by simp)
  have h11 : after 11=cs 11 := extractionInversePrefixStepTemplate_source_frame tm e stride cs 11 (by simp)
  have h17 : after 17=cs 17 := extractionInversePrefixStepTemplate_buffer tm e stride cs
  have hx := extractionInversePrefixStepTemplate_scratch tm e stride cs
  change after 3=2*cs 2 ∧ after 4=cs 1-cs 2-1 ∧ after 7=0 ∧ after 9=0 ∧ after 10=cs 2-1 at hx
  rcases hx with ⟨h3,h4,h7,h9,h10⟩
  have hd := extractionSizeContribution_bound tm (cs 2) (cs 1)
  have hz := extractionInversePrefixStepTemplate_size_scratch tm e stride cs
  change after 5=0 ∧ after 6=0 ∧ after 12=extractionSizeContribution tm (cs 2) (cs 1) ∧
    after 8=extractionSizeContribution tm (cs 2) (cs 1)-3 at hz
  rcases hz with ⟨h5,h6,h12,h8⟩
  have hp := extractionInversePrefixStepTemplate_pointers tm e stride cs
  change after 19=cs 18+extractionSizeContribution tm (cs 2) (cs 1)-5 ∧
    after 21=cs 18+extractionSizeContribution tm (cs 2) (cs 1)-5+1 at hp
  rcases hp with ⟨h19,h21⟩
  have h13 : after 13 ≤ M := hf 13 (by simp)
  have h14 : after 14 ≤ M := hf 14 (by simp)
  have h15 : after 15 ≤ M := hf 15 (by simp)
  have h20 : after 20 ≤ M := ha
  intro q hq2 hq18 hq16
  change after q ≤ M
  fin_cases q <;> simp at * <;> omega

/-- One actual inverse iteration advances the invariant by one spent iteration. -/
theorem extractionInversePrefixBudget_step (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride B M spent : Nat) (cs : ExtractionTermRegister → Nat)
    (h : ExtractionInversePrefixBudget tm e B M spent cs) (hs : spent ≤ B)
    (hsmall : 4*B+(1+(10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7))*B+
      (10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7)+1 ≤ M)
    (hf : ∀ q ∈ ([13,14,15] : List ExtractionTermRegister),
      (extractionInversePrefixStepTemplate tm e stride).counters cs q ≤ M)
    (ha : (extractionInversePrefixStepTemplate tm e stride).counters cs 20 ≤ M) :
    ExtractionInversePrefixBudget tm e B M (spent+1)
      ((extractionInversePrefixStepTemplate tm e stride).counters cs) := by
  refine ⟨?_,?_,?_,extractionInversePrefixStepTemplate_other_budget tm e stride B M spent cs h hs hsmall hf ha,?_⟩
  · intro q hq
    have hb := h.source q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact (extractionInversePrefixStepTemplate_source_frame tm e stride cs 0 (by simp)).trans_le hb
    · exact (extractionInversePrefixStepTemplate_source_frame tm e stride cs 1 (by simp)).trans_le hb
    · exact (extractionInversePrefixStepTemplate_source_frame tm e stride cs 11 (by simp)).trans_le hb
    · exact (extractionInversePrefixStepTemplate_buffer tm e stride cs).trans_le hb
  · rw [(extractionInversePrefixStepTemplate_metadata tm e stride cs).1]
    have hx := h.length; omega
  · rw [(extractionInversePrefixStepTemplate_metadata tm e stride cs).2,Nat.mul_succ]
    have hx := h.base
    have hd := extractionSizeContribution_bound tm (cs 2) (cs 1)
    omega
  · have hc := extractionInversePrefixStepTemplate_schema_count_bound tm e stride cs
    have hx := h.count
    rw [Nat.mul_succ]
    omega

end ShiReversibleGenerator
