import ReversibleExtractionPaddedLeaf
import ReversibleExtractionForwardPassFinalBase
import ReversibleExtractionInversePassFinalBase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionPaddedPassTemplate_base (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat)
    (hell : cs 2=0) (hcount : (if backward then cs 22 else cs 9)=cs 0+1) :
    (extractionPaddedPassTemplate tm e stride backward).counters cs 18=cs 18 := by
  cases backward
  · change cs 9=cs 0+1 at hcount
    have h := extractionPaddedLift_pull (extractionForwardPassTemplate tm e stride) cs 18
    rw [extractionForwardPassTemplate_base tm e stride _ hell hcount] at h
    exact h
  · change cs 22=cs 0+1 at hcount
    have h := extractionPaddedLift_pull (extractionInversePassTemplate tm e stride) cs 18
    rw [extractionInversePassTemplate_base tm e stride _ hell hcount] at h
    exact h

theorem extractionPaddedLeafTemplate_base (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat)
    (hell : cs 2=0) (hcount : (if backward then cs 22 else cs 9)=cs 0+1) :
    (extractionPaddedLeafTemplate tm e stride backward).counters cs 18=cs 18 := by
  cases backward
  · let u := extractionPaddedRootCopyTemplate.counters cs
    have hu : ∀ q : ExtractionPaddedRegister,q ≠ 16 → u q=cs q := by
      intro q hq
      exact Function.update_of_ne hq _ _
    have hu0 := hu 0 (by decide)
    have hu2 := hu 2 (by decide)
    have hu9 := hu 9 (by decide)
    have hu18 := hu 18 (by decide)
    have h := extractionPaddedPassTemplate_base tm e stride false u (hu2.trans hell)
      (by change u 9=u 0+1; rw [hu9,hu0]; exact hcount)
    exact h.trans hu18
  · change extractionPaddedRootCopyTemplate.counters
      ((extractionPaddedPassTemplate tm e stride true).counters cs) 18=cs 18
    rw [extractionPaddedRootCopyTemplate_counters,Function.update_of_ne (by decide : (18 : ExtractionPaddedRegister) ≠ 16)]
    exact extractionPaddedPassTemplate_base tm e stride true cs hell hcount

end ShiReversibleGenerator
