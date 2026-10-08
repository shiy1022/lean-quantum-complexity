import ReversibleExtractionSizeStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

theorem extractionSizeStepTemplate_ready (tm : Turing.FinTM2) (cs : ExtractionSizeRegister → Nat) :
    (extractionSizeStepTemplate tm).ready cs ↔ cs 5=0 ∧ cs 6=0 ∧ cs 7=0 := by
  simp [extractionSizeStepTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    extractionSizeBaseTemplate,extractionSizePayloadTemplate,guardedProgramTemplate,
    extractionSizeGuardRegisters,extractionSizeAdd,counterAffineAccumulationProgramTemplate,
    identityProgramTemplate,AffineAtom.apply]
  split_ifs <;> simp_all <;> tauto

/-- The actual guard-selected arithmetic adds the exact term contribution and caches doubled length. -/
theorem extractionSizeStepTemplate_counters (tm : Turing.FinTM2) (cs : ExtractionSizeRegister → Nat) :
    (extractionSizeStepTemplate tm).counters cs=
      Function.update (Function.update cs 3 (2*cs 2)) 4
        (cs 4+extractionSizeContribution tm (cs 2) (cs 1)) := by
  funext q
  simp [extractionSizeStepTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    extractionSizeBaseTemplate,extractionSizePayloadTemplate,guardedProgramTemplate,
    extractionSizeGuardRegisters,extractionSizeAdd,counterAffineAccumulationProgramTemplate,
    identityProgramTemplate,AffineAtom.apply,TickIndexGuard.eval,TickIndexExpr.eval,
    extractionSizeContribution,Function.update_apply]
  split_ifs <;> simp_all <;> omega

theorem extractionSizeStepTemplate_bytes (tm : Turing.FinTM2) (cs : ExtractionSizeRegister → Nat) :
    (extractionSizeStepTemplate tm).bytes cs=[] := by
  simp [extractionSizeStepTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    extractionSizeBaseTemplate,extractionSizePayloadTemplate,guardedProgramTemplate,
    extractionSizeAdd,counterAffineAccumulationProgramTemplate,identityProgramTemplate]

theorem extractionSizeStepTemplate_remaining_frame (tm : Turing.FinTM2) (cs : ExtractionSizeRegister → Nat) :
    (extractionSizeStepTemplate tm).counters cs 2=cs 2 := by
  rw [extractionSizeStepTemplate_counters]
  simp

theorem extractionSizeStepTemplate_ready_preserved (tm : Turing.FinTM2) (cs : ExtractionSizeRegister → Nat)
    (hr : (extractionSizeStepTemplate tm).ready cs) :
    (extractionSizeStepTemplate tm).ready ((extractionSizeStepTemplate tm).counters cs) := by
  rw [extractionSizeStepTemplate_ready] at hr ⊢
  rw [extractionSizeStepTemplate_counters]
  simpa using hr

end ShiReversibleGenerator
