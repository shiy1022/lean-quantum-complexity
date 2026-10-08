import ReversibleCountedCopyProgramTemplate
import ReversibleCounterPairRetreat

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Source0/target1/count2/buffer3/scratch4/stride5/remaining6/subtract7/dummy8. -/
abbrev OutputCopyRegister := Fin 10

noncomputable def outputCopyRetreatTemplate : CounterProgramTemplate OutputCopyRegister :=
  sequenceProgramTemplate (counterAffineCopyProgramTemplate 5 7 4 0 1 0)
    (sequenceProgramTemplate (counterPairRetreatTemplate 0 8 7) (decrementProgramTemplate 1))

noncomputable def outputCopyStepTemplate : CounterProgramTemplate OutputCopyRegister :=
  sequenceProgramTemplate (countedCopyProgramTemplate 0 1 2 3 4) outputCopyRetreatTemplate

theorem outputCopyRetreatTemplate_embeds : outputCopyRetreatTemplate.Embeds :=
  sequenceProgramTemplate_embeds _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
    (sequenceProgramTemplate_embeds _ _ (counterPairRetreatTemplate_embeds _ _ _)
      (decrementProgramTemplate_embeds _))

theorem outputCopyRetreatTemplate_run : outputCopyRetreatTemplate.Runs := by
  apply sequenceProgramTemplate_run
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · apply counterAffineCopyProgramTemplate_run <;> decide
  · exact sequenceProgramTemplate_run _ _ (counterPairRetreatTemplate_embeds _ _ _)
      (counterPairRetreatTemplate_run _ _ _) (decrementProgramTemplate_run _)

theorem outputCopyStepTemplate_embeds : outputCopyStepTemplate.Embeds :=
  sequenceProgramTemplate_embeds _ _ (countedCopyProgramTemplate_embeds _ _ _ _ _)
    outputCopyRetreatTemplate_embeds

theorem outputCopyStepTemplate_run : outputCopyStepTemplate.Runs := by
  apply sequenceProgramTemplate_run
  · exact countedCopyProgramTemplate_embeds _ _ _ _ _
  · apply countedCopyProgramTemplate_run <;> decide
  · exact outputCopyRetreatTemplate_run

end ShiReversibleGenerator
