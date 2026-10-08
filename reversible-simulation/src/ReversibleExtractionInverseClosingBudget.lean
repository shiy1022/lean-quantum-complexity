import ReversibleExtractionInverseClosingStepBounds

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator

/-- Inverse closing has decreasing term coordinates and growing endpoint and count only. -/
structure ExtractionInverseClosingBudget (tm : Turing.FinTM2) (B M spent : Nat)
    (cs : ExtractionTermRegister → Nat) : Prop where
  source : ∀ q ∈ ([0,1,2,4,9,10,11,17,18] : List ExtractionTermRegister),cs q ≤ B
  endpoint : cs 20 ≤ B+3*spent
  count : cs 16 ≤ B+41*spent
  other : ∀ q,q ≠ 16 → q ≠ 20 → cs q ≤ M

theorem extractionInverseClosingBudget_initial (tm : Turing.FinTM2) (B M : Nat)
    (cs : ExtractionTermRegister → Nat) (hb : ∀ q,cs q ≤ B) (hm : B ≤ M) :
    ExtractionInverseClosingBudget tm B M 0 cs :=
  ⟨fun q _ => hb q,by simpa using hb 20,by simpa using hb 16,fun q _ _ => (hb q).trans hm⟩

theorem extractionInverseClosingBudget_uniform (tm : Turing.FinTM2) (B M spent : Nat)
    (cs : ExtractionTermRegister → Nat) (h : ExtractionInverseClosingBudget tm B M spent cs) :
    ∀ q,cs q ≤ M+B+41*spent := by
  intro q
  by_cases h16 : q=16
  · subst q; have hx := h.count; omega
  by_cases h20 : q=20
  · subst q; have hx := h.endpoint; omega
  exact (h.other q h16 h20).trans (by omega)

theorem extractionInverseClosingBudget_step (tm : Turing.FinTM2) (B M spent : Nat)
    (cs : ExtractionTermRegister → Nat) (h : ExtractionInverseClosingBudget tm B M spent cs)
    (hs : spent ≤ B)
    (hm : 4*B+(10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7)+3 ≤ M) :
    ExtractionInverseClosingBudget tm B M (spent+1) ((extractionInverseClosingStepTemplate tm).counters cs) := by
  let after := (extractionInverseClosingStepTemplate tm).counters cs
  have h0 := h.source 0 (by simp)
  have h1 := h.source 1 (by simp)
  have h2 := h.source 2 (by simp)
  have h4 := h.source 4 (by simp)
  have h9 := h.source 9 (by simp)
  have h10 := h.source 10 (by simp)
  have h11 := h.source 11 (by simp)
  have h17 := h.source 17 (by simp)
  have h18 := h.source 18 (by simp)
  have he := h.endpoint
  have hc := h.count
  have he4 : cs 20 ≤ 4*B := by omega
  have hmeta := extractionInverseClosingStepTemplate_metadata tm cs
  change after 2=cs 2-1 ∧ after 18=cs 18-(extractionSizeContribution tm (cs 2) (cs 1)-3) ∧ after 20=cs 20+3 at hmeta
  rcases hmeta with ⟨hx2,hx18,hx20⟩
  have hf : ∀ q ∈ ([0,1,4,9,10,11,17] : List ExtractionTermRegister),after q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact extractionInverseClosingStepTemplate_source_frame tm cs 0 (by simp)
    · exact extractionInverseClosingStepTemplate_source_frame tm cs 1 (by simp)
    · exact extractionInverseClosingStepTemplate_extra_frame tm cs 4 (by simp)
    · exact extractionInverseClosingStepTemplate_extra_frame tm cs 9 (by simp)
    · exact extractionInverseClosingStepTemplate_extra_frame tm cs 10 (by simp)
    · exact extractionInverseClosingStepTemplate_source_frame tm cs 11 (by simp)
    · exact extractionInverseClosingStepTemplate_source_frame tm cs 17 (by simp)
  have hx0 := hf 0 (by simp)
  have hx1 := hf 1 (by simp)
  have hx4 := hf 4 (by simp)
  have hx9 := hf 9 (by simp)
  have hx10 := hf 10 (by simp)
  have hx11 := hf 11 (by simp)
  have hx17 := hf 17 (by simp)
  have hw := extractionInverseClosingStepTemplate_overwritten tm cs B (4*B) h2 (by omega) he4
  change after 3 ≤ 2*B ∧ after 5=0 ∧ after 6=0 ∧ after 7=0 ∧ after 8=0 ∧
    after 12 ≤ _ ∧ after 13 ≤ _ ∧ after 14 ≤ _ ∧ after 15 ≤ _ ∧ after 19 ≤ _ ∧ after 21 ≤ _ at hw
  rcases hw with ⟨hx3,hx5,hx6,hx7,hx8,hx12,hx13,hx14,hx15,hx19,hx21⟩
  change ExtractionInverseClosingBudget tm B M (spent+1) after
  refine ⟨?_,?_,?_,?_⟩
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · rw [hx20,Nat.mul_succ]; omega
  · have hx := extractionInverseClosingStepTemplate_count tm cs
    change after 16=cs 16+41 at hx
    rw [Nat.mul_succ]; omega
  · intro q hq16 hq20
    change after q ≤ M
    fin_cases q <;> simp at * <;> omega

end ShiReversibleGenerator
