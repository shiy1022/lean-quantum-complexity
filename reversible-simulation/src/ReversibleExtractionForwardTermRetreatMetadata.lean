import ReversibleExtractionForwardTermRetreatCounters

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Retreat changes the two pointers and scratch, while framing every runtime source parameter. -/
theorem extractionForwardTermRetreatTemplate_frame (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) (q : ExtractionTermRegister)
    (h3 : q ≠ 3) (h5 : q ≠ 5) (h6 : q ≠ 6) (h7 : q ≠ 7) (h8 : q ≠ 8)
    (h12 : q ≠ 12) (h18 : q ≠ 18) (h20 : q ≠ 20) :
    (extractionForwardTermRetreatTemplate tm).counters cs q=cs q := by
  simp [extractionForwardTermRetreatTemplate_counters,
    extractionTermSizeProgramTemplate_counters,cleanupCounters_apply,
    h3,h5,h6,h7,h8,h12,h18,h20]

theorem extractionForwardTermRetreatTemplate_base (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) :
    (extractionForwardTermRetreatTemplate tm).counters cs 18=
      cs 18-(extractionSizeContribution tm (cs 2) (cs 1)-3) := by
  simp [extractionForwardTermRetreatTemplate_counters,
    extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]

theorem extractionForwardTermRetreatTemplate_size (tm : Turing.FinTM2)
    (cs : ExtractionTermRegister → Nat) :
    (extractionForwardTermRetreatTemplate tm).counters cs 12=
      extractionSizeContribution tm (cs 2) (cs 1) := by
  simp [extractionForwardTermRetreatTemplate_counters,
    extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]

end ShiReversibleGenerator
