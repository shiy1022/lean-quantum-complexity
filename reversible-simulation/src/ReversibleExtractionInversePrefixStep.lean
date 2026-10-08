import ReversibleExtractionPrefixAdvance
import ReversibleExtractionForwardPrefixStep

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Because printing prepends, an inverse prefix body prints the inverse term before its inverse negation. -/
noncomputable def extractionInversePrefixStepTemplate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :=
  sequenceProgramTemplate (extractionTermSizeProgramTemplate tm)
    (sequenceProgramTemplate (extractionBoundTermPrinterTemplate tm e stride true)
      (sequenceProgramTemplate (extractionTermNegationPrinterTemplate true) extractionPrefixAdvanceTemplate))

theorem extractionInversePrefixStepTemplate_embeds (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :
    (extractionInversePrefixStepTemplate tm e stride).Embeds := by
  unfold extractionInversePrefixStepTemplate
  exact sequenceProgramTemplate_embeds _ _ (extractionTermSizeProgramTemplate_embeds tm)
    (sequenceProgramTemplate_embeds _ _ (extractionBoundTermPrinterTemplate_embeds tm e stride true)
      (sequenceProgramTemplate_embeds _ _ (extractionTermNegationPrinterTemplate_embeds true)
        extractionPrefixAdvanceTemplate_embeds))

theorem extractionInversePrefixStepTemplate_run (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :
    (extractionInversePrefixStepTemplate tm e stride).Runs := by
  unfold extractionInversePrefixStepTemplate
  exact sequenceProgramTemplate_run _ _ (extractionTermSizeProgramTemplate_embeds tm)
    (extractionTermSizeProgramTemplate_run tm)
    (sequenceProgramTemplate_run _ _ (extractionBoundTermPrinterTemplate_embeds tm e stride true)
      (extractionBoundTermPrinterTemplate_run tm e stride true)
      (sequenceProgramTemplate_run _ _ (extractionTermNegationPrinterTemplate_embeds true)
        (extractionTermNegationPrinterTemplate_run true) extractionPrefixAdvanceTemplate_run))

end ShiReversibleGenerator
