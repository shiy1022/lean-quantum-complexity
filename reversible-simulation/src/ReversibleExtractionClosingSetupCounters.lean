import ReversibleExtractionClosingSetup

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

theorem extractionClosingSetupTemplate_counters (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionClosingSetupTemplate tm).counters cs=
      Function.update (Function.update ((extractionTermSizeProgramTemplate tm).counters cs)
        19 (cs 18+extractionSizeContribution tm (cs 2) (cs 1)-4)) 21 (cs 20-3) := by
  change extractionClosingPointerTemplate.counters ((extractionTermSizeProgramTemplate tm).counters cs)=_
  rw [extractionClosingPointerTemplate_counters]
  simp [extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]

theorem extractionClosingSetupTemplate_ready (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionClosingSetupTemplate tm).ready cs := by
  refine ⟨extractionTermSizeProgramTemplate_ready tm cs,extractionClosingPointerTemplate_ready _ ?_⟩
  simp [extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]

theorem extractionClosingSetupTemplate_bytes (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionClosingSetupTemplate tm).bytes cs=[] := by
  simp [extractionClosingSetupTemplate,sequenceProgramTemplate,extractionTermSizeProgramTemplate_bytes,
    extractionClosingPointerTemplate_bytes]

end ShiReversibleGenerator
