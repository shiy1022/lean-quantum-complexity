import ReversibleExtractionInverseClosingRetreatCounters

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Retreat changes the two pointers and scratch, while framing every runtime source parameter. -/
theorem extractionInverseClosingRetreatTemplate_frame (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) (q : ExtractionTermRegister)
    (h3 : q ≠ 3) (h5 : q ≠ 5) (h6 : q ≠ 6) (h7 : q ≠ 7) (h8 : q ≠ 8)
    (h12 : q ≠ 12) (h18 : q ≠ 18) (h19 : q ≠ 19) :
    (extractionInverseClosingRetreatTemplate tm).counters cs q=cs q := by
  simp [extractionInverseClosingRetreatTemplate_counters,
    extractionTermSizeProgramTemplate_counters,cleanupCounters_apply,
    h3,h5,h6,h7,h8,h12,h18,h19]

theorem extractionInverseClosingRetreatTemplate_base (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) :
    (extractionInverseClosingRetreatTemplate tm).counters cs 18=
      cs 18-(extractionSizeContribution tm (cs 2) (cs 1)-3) := by
  simp [extractionInverseClosingRetreatTemplate_counters,
    extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]

theorem extractionInverseClosingRetreatTemplate_size (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) :
    (extractionInverseClosingRetreatTemplate tm).counters cs 12=
      extractionSizeContribution tm (cs 2) (cs 1) := by
  simp [extractionInverseClosingRetreatTemplate_counters,
    extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]

end ShiReversibleGenerator
