import ReversibleExtractionTraversalRegisterInjection
import ReversibleExtractionTermNegationCertificate
import ReversibleExtractionForwardTermRetreat
import ReversibleExtractionBoundTermCertificate
import ReversibleDecrementProgramTemplate

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Runtime printing prepends bytes: print the negation before its term, then descend in length. -/
noncomputable def extractionForwardPrefixStepTemplate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :=
  sequenceProgramTemplate (extractionForwardTermRetreatTemplate tm)
    (sequenceProgramTemplate (extractionTermNegationPrinterTemplate false)
      (sequenceProgramTemplate (extractionBoundTermPrinterTemplate tm e stride false)
        (decrementProgramTemplate (2 : ExtractionTermRegister))))

theorem extractionForwardPrefixStepTemplate_embeds (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :
    (extractionForwardPrefixStepTemplate tm e stride).Embeds := by
  unfold extractionForwardPrefixStepTemplate
  apply sequenceProgramTemplate_embeds
  · exact extractionForwardTermRetreatTemplate_embeds tm
  · apply sequenceProgramTemplate_embeds
    · exact extractionTermNegationPrinterTemplate_embeds false
    · apply sequenceProgramTemplate_embeds
      · exact extractionBoundTermPrinterTemplate_embeds tm e stride false
      · exact decrementProgramTemplate_embeds _

theorem extractionForwardPrefixStepTemplate_run (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :
    (extractionForwardPrefixStepTemplate tm e stride).Runs := by
  unfold extractionForwardPrefixStepTemplate
  apply sequenceProgramTemplate_run
  · exact extractionForwardTermRetreatTemplate_embeds tm
  · exact extractionForwardTermRetreatTemplate_run tm
  · apply sequenceProgramTemplate_run
    · exact extractionTermNegationPrinterTemplate_embeds false
    · exact extractionTermNegationPrinterTemplate_run false
    · apply sequenceProgramTemplate_run
      · exact extractionBoundTermPrinterTemplate_embeds tm e stride false
      · exact extractionBoundTermPrinterTemplate_run tm e stride false
      · exact decrementProgramTemplate_run _

noncomputable def extractionForwardPrefixTraversalStepTemplate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :=
  extractionTraversalLift (extractionForwardPrefixStepTemplate tm e stride)

theorem extractionForwardPrefixTraversalStepTemplate_run (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :
    (extractionForwardPrefixTraversalStepTemplate tm e stride).Runs :=
  extractionTraversalLift_run _ (extractionForwardPrefixStepTemplate_embeds tm e stride)
    (extractionForwardPrefixStepTemplate_run tm e stride)

end ShiReversibleGenerator
