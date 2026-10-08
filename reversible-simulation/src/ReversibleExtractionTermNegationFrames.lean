import ReversibleExtractionTermNegationCertificate

set_option autoImplicit false
namespace ShiReversibleGenerator

theorem extractionTermNegationPrinterTemplate_frame (backward : Bool)
    (cs : ExtractionTermRegister → Nat) (q : ExtractionTermRegister)
    (h13 : q ≠ 13) (h14 : q ≠ 14) (h15 : q ≠ 15) (h16 : q ≠ 16)
    (h19 : q ≠ 19) (h21 : q ≠ 21) :
    (extractionTermNegationPrinterTemplate backward).counters cs q=cs q := by
  change fixedNodeCounters extractionTermNodeRegisters _
    (extractionTermNegationSetupTemplate.counters cs) q=_
  rw [fixedNodeCounters_other _ _ q h13 h14 h15 h16]
  simp only [extractionTermNegationSetupTemplate_counters,Function.update_of_ne h21,
    Function.update_of_ne h19]

end ShiReversibleGenerator
