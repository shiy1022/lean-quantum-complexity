import ReversibleExtractionForwardPrefixStepReady
import ReversibleExtractionForwardTermRetreatMetadata

set_option autoImplicit false
namespace ShiReversibleGenerator

theorem extractionForwardPrefixStepTemplate_frame (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat)
    (q : ExtractionTermRegister)
    (h2 : q ≠ 2) (h3 : q ≠ 3) (h4 : q ≠ 4) (h5 : q ≠ 5) (h6 : q ≠ 6)
    (h7 : q ≠ 7) (h8 : q ≠ 8) (h9 : q ≠ 9) (h10 : q ≠ 10) (h12 : q ≠ 12)
    (h13 : q ≠ 13) (h14 : q ≠ 14) (h15 : q ≠ 15) (h16 : q ≠ 16)
    (h18 : q ≠ 18) (h19 : q ≠ 19) (h20 : q ≠ 20) (h21 : q ≠ 21) :
    (extractionForwardPrefixStepTemplate tm e stride).counters cs q=cs q := by
  change (decrementProgramTemplate (2 : ExtractionTermRegister)).counters
    ((extractionBoundTermPrinterTemplate tm e stride false).counters
      ((extractionTermNegationPrinterTemplate false).counters
        ((extractionForwardTermRetreatTemplate tm).counters cs))) q=_
  simp only [decrementProgramTemplate,Function.update_of_ne h2]
  rw [extractionBoundTermPrinterTemplate_frame _ _ _ _ _ _ h3 h4 h7 h8 h9 h10 h13 h14 h15 h16 h19 h20 h21,
    extractionTermNegationPrinterTemplate_frame _ _ _ h13 h14 h15 h16 h19 h21,
    extractionForwardTermRetreatTemplate_frame _ _ _ h3 h5 h6 h7 h8 h12 h18 h20]

theorem extractionForwardPrefixStepTemplate_length (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) :
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 2=cs 2-1 := by
  change (decrementProgramTemplate (2 : ExtractionTermRegister)).counters
    ((extractionBoundTermPrinterTemplate tm e stride false).counters
      ((extractionTermNegationPrinterTemplate false).counters
        ((extractionForwardTermRetreatTemplate tm).counters cs))) 2=_
  simp only [decrementProgramTemplate,Function.update_self]
  rw [extractionBoundTermPrinterTemplate_frame _ _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    extractionTermNegationPrinterTemplate_frame _ _ _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    extractionForwardTermRetreatTemplate_frame _ _ _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]

end ShiReversibleGenerator
