import ReversibleExtractionPaddedLeaf
import ReversibleExtractionInversePassScratch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Both actual leaf graphs are ready from zero emitter scratch and buffer, without an exit-readiness premise. -/
theorem extractionPaddedLeafTemplate_ready (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat)
    (h17 : cs 17=0) (h7 : cs 7=0) : (extractionPaddedLeafTemplate tm e stride backward).ready cs := by
  cases backward
  · change extractionPaddedRootCopyTemplate.ready cs ∧
      (extractionPaddedPassTemplate tm e stride false).ready (extractionPaddedRootCopyTemplate.counters cs) ∧ True
    refine ⟨extractionPaddedRootCopyTemplate_ready cs h17 h7,?_,trivial⟩
    apply extractionPaddedPassTemplate_ready tm e stride false
    simpa only [extractionPaddedRootCopyTemplate_counters,Function.update_of_ne (by decide : (17 : ExtractionPaddedRegister) ≠ 16)] using h17
  · let u := (extractionPaddedPassTemplate tm e stride true).counters cs
    let small := fun r => cs (extractionTraversalToPaddedRegister r)
    have hs := extractionInversePassTemplate_scratch tm e stride small
    have hu7 : u 7=0 := by
      have h := extractionPaddedLift_pull (extractionInversePassTemplate tm e stride) cs 7
      rw [hs.1] at h
      exact h
    have hu17 : u 17=0 := by
      have h := extractionPaddedLift_pull (extractionInversePassTemplate tm e stride) cs 17
      rw [hs.2] at h
      exact h.trans h17
    change (extractionPaddedPassTemplate tm e stride true).ready cs ∧ extractionPaddedRootCopyTemplate.ready u ∧ True
    exact ⟨extractionPaddedPassTemplate_ready tm e stride true cs h17,
      extractionPaddedRootCopyTemplate_ready u hu17 hu7,trivial⟩

end ShiReversibleGenerator
