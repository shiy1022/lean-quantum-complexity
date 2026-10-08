import ReversibleExtractionForwardPrefixStepFrames

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Printing preserves the retreat result's base and runtime source parameters. -/
theorem extractionForwardPrefixStepTemplate_retreat_frame (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat)
    (q : ExtractionTermRegister) (h2 : q ≠ 2) (h3 : q ≠ 3) (h4 : q ≠ 4)
    (h7 : q ≠ 7) (h8 : q ≠ 8) (h9 : q ≠ 9) (h10 : q ≠ 10)
    (h13 : q ≠ 13) (h14 : q ≠ 14) (h15 : q ≠ 15) (h16 : q ≠ 16)
    (h19 : q ≠ 19) (h20 : q ≠ 20) (h21 : q ≠ 21) :
    (extractionForwardPrefixStepTemplate tm e stride).counters cs q=
      (extractionForwardTermRetreatTemplate tm).counters cs q := by
  change (decrementProgramTemplate (2 : ExtractionTermRegister)).counters
    ((extractionBoundTermPrinterTemplate tm e stride false).counters
      ((extractionTermNegationPrinterTemplate false).counters
        ((extractionForwardTermRetreatTemplate tm).counters cs))) q=_
  simp only [decrementProgramTemplate,Function.update_of_ne h2]
  rw [extractionBoundTermPrinterTemplate_frame _ _ _ _ _ _ h3 h4 h7 h8 h9 h10 h13 h14 h15 h16 h19 h20 h21,
    extractionTermNegationPrinterTemplate_frame _ _ _ h13 h14 h15 h16 h19 h21]

theorem extractionForwardPrefixStepTemplate_base (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) :
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 18=
      cs 18-(extractionSizeContribution tm (cs 2) (cs 1)-3) := by
  rw [extractionForwardPrefixStepTemplate_retreat_frame _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact extractionForwardTermRetreatTemplate_base tm cs

end ShiReversibleGenerator
