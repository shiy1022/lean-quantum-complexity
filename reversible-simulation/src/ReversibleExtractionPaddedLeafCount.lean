import ReversibleExtractionPaddedLeaf
import ReversibleExtractionForwardPassCount
import ReversibleExtractionPassLayerCount
import ReversibleInitializationExactLayers
import ReversibleExtractionNaturalFormulaAgreement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

theorem extractionPaddedPassTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat)
    (hell : cs 2=0) (hcount : (if backward then cs 22 else cs 9)=cs 0+1) :
    (extractionPaddedPassTemplate tm e stride backward).counters cs 16=cs 16+
      formulaElementaryLayers (extractionFormula tm e (cs 0) (cs 1)) := by
  cases backward
  · change cs 9=cs 0+1 at hcount
    have h := extractionPaddedLift_pull (extractionForwardPassTemplate tm e stride) cs 16
    rw [extractionForwardPassTemplate_count tm e stride _ hcount,
      extractionNaturalFormula_original,formulaElementaryLayers_rename] at h
    exact h
  · change cs 22=cs 0+1 at hcount
    have h := extractionPaddedLift_pull (extractionInversePassTemplate tm e stride) cs 16
    rw [extractionInversePassTemplate_count tm e stride _ hell hcount,
      extractionNaturalFormula_original,formulaElementaryLayers_rename] at h
    exact h

/-- The real leaf counter includes exactly one additional elementary CNOT for its padded root. -/
theorem extractionPaddedLeafTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat)
    (hell : cs 2=0) (hcount : (if backward then cs 22 else cs 9)=cs 0+1) :
    (extractionPaddedLeafTemplate tm e stride backward).counters cs 16=cs 16+
      (formulaElementaryLayers (extractionFormula tm e (cs 0) (cs 1))+1) := by
  cases backward
  · change cs 9=cs 0+1 at hcount
    let u := extractionPaddedRootCopyTemplate.counters cs
    have hu : ∀ q : ExtractionPaddedRegister,q ≠ 16 → u q=cs q := by
      intro q hq
      exact Function.update_of_ne hq _ _
    have hu0 := hu 0 (by decide)
    have hu1 := hu 1 (by decide)
    have hu2 := hu 2 (by decide)
    have hu9 := hu 9 (by decide)
    have hu16 : u 16=cs 16+1 := by simp only [u,extractionPaddedRootCopyTemplate_counters,Function.update_self]
    have hc := extractionPaddedPassTemplate_count tm e stride false u
      (hu2.trans hell) (by change u 9=u 0+1; rw [hu9,hu0]; exact hcount)
    rw [hu0,hu1,hu16] at hc
    change (extractionPaddedPassTemplate tm e stride false).counters u 16=_
    omega
  · change extractionPaddedRootCopyTemplate.counters
      ((extractionPaddedPassTemplate tm e stride true).counters cs) 16=_
    rw [extractionPaddedRootCopyTemplate_counters,Function.update_self,
      extractionPaddedPassTemplate_count tm e stride true cs hell hcount]
    omega

end ShiReversibleGenerator
