import ReversibleExtractionSizeContribution
import ReversibleCounterAffineProgramTemplates
import ReversibleCleanupProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Capacity, output position, length-loop counter, doubled length, accumulated suffix size,
guard scratch, guard scratch, affine scratch; remaining registers are reserved. -/
abbrev ExtractionSizeRegister := Fin 12

noncomputable def extractionSizeGuardRegisters (ell : ExtractionSizeRegister) : GuardProgramRegisters ExtractionSizeRegister :=
  ⟨ell,1,5,6,7⟩

noncomputable def extractionSizeAdd (amount : Nat) : CounterProgramTemplate ExtractionSizeRegister :=
  counterAffineAccumulationProgramTemplate ⟨2,4,amount,0⟩ 7

noncomputable def extractionSizeBaseTemplate : CounterProgramTemplate ExtractionSizeRegister :=
  guardedProgramTemplate (extractionSizeGuardRegisters 2) ⟨.capacity,.literal 0⟩
    (extractionSizeAdd 9) (extractionSizeAdd 10)

noncomputable def extractionSizePayloadTemplate (tm : Turing.FinTM2) : CounterProgramTemplate ExtractionSizeRegister :=
  guardedProgramTemplate (extractionSizeGuardRegisters 2) ⟨.add .capacity 1,.position⟩
    (guardedProgramTemplate (extractionSizeGuardRegisters 3) ⟨.position,.capacity⟩
      (extractionSizeAdd (Fintype.card (Option (MachineSymbol tm))*7)) identityProgramTemplate)
    identityProgramTemplate

noncomputable def extractionSizeStepTemplate (tm : Turing.FinTM2) : CounterProgramTemplate ExtractionSizeRegister :=
  sequenceProgramTemplate (counterAffineCopyProgramTemplate 2 3 7 0 2 0)
    (sequenceProgramTemplate extractionSizeBaseTemplate (extractionSizePayloadTemplate tm))

theorem extractionSizeStepTemplate_embeds (tm : Turing.FinTM2) : (extractionSizeStepTemplate tm).Embeds := by
  apply sequenceProgramTemplate_embeds
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · apply sequenceProgramTemplate_embeds
    · exact guardedProgramTemplate_embeds _ _ _ _
        (counterAffineAccumulationProgramTemplate_embeds _ _) (counterAffineAccumulationProgramTemplate_embeds _ _)
    · apply guardedProgramTemplate_embeds
      · exact guardedProgramTemplate_embeds _ _ _ _ (counterAffineAccumulationProgramTemplate_embeds _ _)
          identityProgramTemplate_embeds
      · exact identityProgramTemplate_embeds

theorem extractionSizeStepTemplate_run (tm : Turing.FinTM2) : (extractionSizeStepTemplate tm).Runs := by
  apply sequenceProgramTemplate_run
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact counterAffineCopyProgramTemplate_run _ _ _ _ _ _ (by decide) (by decide) (by decide)
  · apply sequenceProgramTemplate_run
    · exact guardedProgramTemplate_embeds _ _ _ _
        (counterAffineAccumulationProgramTemplate_embeds _ _) (counterAffineAccumulationProgramTemplate_embeds _ _)
    · exact guardedProgramTemplate_run _ _ _ _ (by constructor <;> decide)
        (counterAffineAccumulationProgramTemplate_embeds _ _)
        (counterAffineAccumulationProgramTemplate_run _ _ (by simp [AffineAtom.Valid]))
        (counterAffineAccumulationProgramTemplate_run _ _ (by simp [AffineAtom.Valid]))
    · apply guardedProgramTemplate_run _ _ _ _ (by constructor <;> decide)
      · exact guardedProgramTemplate_embeds _ _ _ _ (counterAffineAccumulationProgramTemplate_embeds _ _)
          identityProgramTemplate_embeds
      · exact guardedProgramTemplate_run _ _ _ _ (by constructor <;> decide)
          (counterAffineAccumulationProgramTemplate_embeds _ _)
          (counterAffineAccumulationProgramTemplate_run _ _ (by simp [AffineAtom.Valid])) identityProgramTemplate_run
      · exact identityProgramTemplate_run

end ShiReversibleGenerator
