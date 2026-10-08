import ReversibleExtractionPrefixLoopBudgetData
import ReversibleExtractionTermSizeBudget

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator

/-- Once fields and input addresses have a fixed budget, every other prefix counter stays bounded. -/
theorem extractionForwardPrefixStepTemplate_other_budget (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride B M : Nat) (cs : ExtractionTermRegister → Nat)
    (hb : ∀ q ∈ ([0,1,2,11,18] : List ExtractionTermRegister),cs q ≤ B)
    (h17 : cs 17 ≤ M) (hsmall : 2*B+(10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7) ≤ M)
    (hf : ∀ q ∈ ([13,14,15] : List ExtractionTermRegister),
      (extractionForwardPrefixStepTemplate tm e stride).counters cs q ≤ M)
    (ha : ∀ q ∈ ([19,20,21] : List ExtractionTermRegister),
      (extractionForwardPrefixStepTemplate tm e stride).counters cs q ≤ M) :
    ∀ q,q ≠ 16 → (extractionForwardPrefixStepTemplate tm e stride).counters cs q ≤ M := by
  let after := (extractionForwardPrefixStepTemplate tm e stride).counters cs
  have hb0 := hb 0 (by simp)
  have hb1 := hb 1 (by simp)
  have hb2 := hb 2 (by simp)
  have hb11 := hb 11 (by simp)
  have hb18 := hb 18 (by simp)
  have hstable : ∀ q ∈ ([0,1,11,17] : List ExtractionTermRegister),after q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals exact (extractionForwardPrefixStepTemplate_frame tm e stride cs _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have h0 := hstable 0 (by simp)
  have h1 := hstable 1 (by simp)
  have h11 := hstable 11 (by simp)
  have hx17 := hstable 17 (by simp)
  have h2 : after 2=cs 2-1 := extractionForwardPrefixStepTemplate_length tm e stride cs
  have h18 : after 18=cs 18-(extractionSizeContribution tm (cs 2) (cs 1)-3) :=
    extractionForwardPrefixStepTemplate_base tm e stride cs
  have hx := extractionForwardPrefixStepTemplate_scratch tm e stride cs
  change after 3=2*cs 2 ∧ after 4=cs 1-cs 2-1 ∧ after 7=0 ∧ after 8=0 ∧ after 9=0 ∧ after 10=cs 2-1 at hx
  rcases hx with ⟨h3,h4,h7,h8,h9,h10⟩
  have hs := extractionForwardPrefixStepTemplate_size_scratch tm e stride cs
  change after 5=0 ∧ after 6=0 ∧ after 12=extractionSizeContribution tm (cs 2) (cs 1) at hs
  rcases hs with ⟨h5,h6,h12⟩
  have hd := extractionSizeContribution_bound tm (cs 2) (cs 1)
  have h13 : after 13 ≤ M := hf 13 (by simp)
  have h14 : after 14 ≤ M := hf 14 (by simp)
  have h15 : after 15 ≤ M := hf 15 (by simp)
  have h19 : after 19 ≤ M := ha 19 (by simp)
  have h20 : after 20 ≤ M := ha 20 (by simp)
  have h21 : after 21 ≤ M := ha 21 (by simp)
  intro q hq
  change after q ≤ M
  fin_cases q <;> simp at * <;> omega

theorem extractionPrefixLoopBudget_step (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride B M spent : Nat) (cs : ExtractionTermRegister → Nat)
    (h : ExtractionPrefixLoopBudget tm e B M spent cs)
    (hsmall : 2*B+(10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7) ≤ M)
    (hf : ∀ q ∈ ([13,14,15] : List ExtractionTermRegister),
      (extractionForwardPrefixStepTemplate tm e stride).counters cs q ≤ M)
    (ha : ∀ q ∈ ([19,20,21] : List ExtractionTermRegister),
      (extractionForwardPrefixStepTemplate tm e stride).counters cs q ≤ M) :
    ExtractionPrefixLoopBudget tm e B M (spent+1) ((extractionForwardPrefixStepTemplate tm e stride).counters cs) := by
  refine ⟨?_,extractionForwardPrefixStepTemplate_other_budget tm e stride B M cs h.metadata
    (h.other 17 (by decide)) hsmall hf ha,?_⟩
  · intro q hq
    have hb := h.metadata q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact (extractionForwardPrefixStepTemplate_frame tm e stride cs _
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans_le hb
      | exact (extractionForwardPrefixStepTemplate_length tm e stride cs).trans_le ((Nat.sub_le _ _).trans hb)
      | exact (extractionForwardPrefixStepTemplate_base tm e stride cs).trans_le ((Nat.sub_le _ _).trans hb)
  · have hc := extractionForwardPrefixStepTemplate_schema_count_bound tm e stride cs
    have hp := h.count
    rw [Nat.mul_succ]
    omega

end ShiReversibleGenerator
