import ReversibleExtractionForwardPrefixScratchMetadata
import ReversibleExtractionPrefixSchemaCountBound

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Prefix iteration separates stable metadata and overwritten fields from the accumulating count. -/
structure ExtractionPrefixLoopBudget (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M spent : Nat) (cs : ExtractionTermRegister → Nat) : Prop where
  metadata : ∀ q ∈ ([0,1,2,11,18] : List ExtractionTermRegister),cs q ≤ B
  other : ∀ q,q ≠ 16 → cs q ≤ M
  count : cs 16 ≤ B+(37*extractionTermSchemaBudget tm e+2)*spent

theorem extractionPrefixLoopBudget_initial (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M : Nat) (cs : ExtractionTermRegister → Nat) (hb : ∀ q,cs q ≤ B) (hm : B ≤ M) :
    ExtractionPrefixLoopBudget tm e B M 0 cs := by
  exact ⟨fun q _ => hb q,fun q _ => (hb q).trans hm,by simpa using hb 16⟩

theorem extractionPrefixLoopBudget_uniform (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (B M spent : Nat) (cs : ExtractionTermRegister → Nat) (h : ExtractionPrefixLoopBudget tm e B M spent cs) :
    ∀ q,cs q ≤ M+B+(37*extractionTermSchemaBudget tm e+2)*spent := by
  intro q
  by_cases hq : q=16
  · subst q
    exact h.count.trans (by omega)
  · exact (h.other q hq).trans (by omega)

end ShiReversibleGenerator
