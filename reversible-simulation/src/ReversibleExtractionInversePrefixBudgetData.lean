import ReversibleExtractionInversePrefixSchemaCountBound
import ReversibleExtractionInversePrefixTraversalMetadata

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Ascending inverse extraction separates its two growing coordinates from stable scratch. -/
structure ExtractionInversePrefixBudget (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M spent : Nat) (cs : ExtractionTermRegister → Nat) : Prop where
  source : ∀ q ∈ ([0,1,11,17] : List ExtractionTermRegister),cs q ≤ B
  length : cs 2 ≤ B+spent
  base : cs 18 ≤ B+(10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7)*spent
  other : ∀ q,q ≠ 2 → q ≠ 18 → q ≠ 16 → cs q ≤ M
  count : cs 16 ≤ B+(37*extractionTermSchemaBudget tm e+2)*spent

theorem extractionInversePrefixBudget_initial (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M : Nat) (cs : ExtractionTermRegister → Nat) (hb : ∀ q,cs q ≤ B) (hm : B ≤ M) :
    ExtractionInversePrefixBudget tm e B M 0 cs := by
  exact ⟨fun q _ => hb q,by simpa using hb 2,by simpa using hb 18,
    fun q _ _ _ => (hb q).trans hm,by simpa using hb 16⟩

theorem extractionInversePrefixBudget_uniform (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M spent : Nat) (cs : ExtractionTermRegister → Nat)
    (h : ExtractionInversePrefixBudget tm e B M spent cs) :
    ∀ q,cs q ≤ M+B+
      (10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7+37*extractionTermSchemaBudget tm e+3)*spent := by
  intro q
  have h2 := h.length
  have h18 := h.base
  have h16 := h.count
  by_cases hq2 : q=2
  · subst q; nlinarith
  by_cases hq18 : q=18
  · subst q; nlinarith
  by_cases hq16 : q=16
  · subst q; nlinarith
  exact (h.other q hq2 hq18 hq16).trans (by omega)

/-- At most B iterations give a single source budget and a single growing-base budget. -/
theorem extractionInversePrefixBudget_sources (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M spent : Nat) (cs : ExtractionTermRegister → Nat)
    (h : ExtractionInversePrefixBudget tm e B M spent cs) (hs : spent ≤ B) :
    (∀ q ∈ ([0,1,2,11] : List ExtractionTermRegister),cs q ≤ 2*B) ∧
      cs 18 ≤ (1+(10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7))*B := by
  refine ⟨?_,?_⟩
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact (h.source 0 (by simp)).trans (by omega)
    · exact (h.source 1 (by simp)).trans (by omega)
    · have hx := h.length; omega
    · exact (h.source 11 (by simp)).trans (by omega)
  · have hx := h.base
    have hm := Nat.mul_le_mul_left (10+Fintype.card (Option (ShiReversibleTM.MachineSymbol tm))*7) hs
    nlinarith

end ShiReversibleGenerator
