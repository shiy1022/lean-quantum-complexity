import ReversibleExtractionBoundClosingPrinter
import ReversibleFormulaPrinterRun

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Closing emission preserves the capacity, output position, length index and both outer loop pointers. -/
theorem extractionBoundClosingPrinterTemplate_frame (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) (q : ExtractionTermRegister)
    (h3 : q ≠ 3) (h5 : q ≠ 5) (h6 : q ≠ 6) (h7 : q ≠ 7) (h12 : q ≠ 12)
    (h13 : q ≠ 13) (h14 : q ≠ 14) (h15 : q ≠ 15) (h16 : q ≠ 16)
    (h19 : q ≠ 19) (h21 : q ≠ 21) :
    (extractionBoundClosingPrinterTemplate tm backward).counters cs q=cs q := by
  change fixedNodeCounters extractionTermNodeRegisters _ ((extractionClosingSetupTemplate tm).counters cs) q=_
  rw [fixedNodeCounters_other _ _ q h13 h14 h15 h16]
  simp [extractionClosingSetupTemplate_counters,extractionTermSizeProgramTemplate_counters,
    cleanupCounters_apply,h3,h5,h6,h7,h12,h19,h21]

theorem extractionBoundClosingPrinterTemplate_scratch (tm : Turing.FinTM2) (backward : Bool)
    (cs : ExtractionTermRegister → Nat) :
    (extractionBoundClosingPrinterTemplate tm backward).counters cs 7=0 := by
  change fixedNodeCounters extractionTermNodeRegisters _ ((extractionClosingSetupTemplate tm).counters cs) 7=_
  rw [fixedNodeCounters_other _ _ 7 (by simp [extractionTermNodeRegisters])
    (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters])]
  simp [extractionClosingSetupTemplate_counters,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]

end ShiReversibleGenerator
