import ReversibleExtractionTermNegationSetup
import ReversibleExtractionClosingCertificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The real term-negation assignment, printed only after its runtime root and fresh target are bound. -/
noncomputable def extractionTermNegationPrinterTemplate (backward : Bool) :=
  sequenceProgramTemplate extractionTermNegationSetupTemplate
    (fixedNodeProgramTemplate extractionTermNodeRegisters
      [symbolicAssignmentTemplate backward (.neg ⟨19,0⟩ ⟨21,0⟩)])

theorem extractionTermNegationPrinterTemplate_embeds (backward : Bool) :
    (extractionTermNegationPrinterTemplate backward).Embeds :=
  sequenceProgramTemplate_embeds _ _ extractionTermNegationSetupTemplate_embeds
    (fixedNodeProgramTemplate_embeds _ _)

theorem extractionTermNegationPrinterTemplate_run (backward : Bool) :
    (extractionTermNegationPrinterTemplate backward).Runs := by
  apply sequenceProgramTemplate_run
  · exact extractionTermNegationSetupTemplate_embeds
  · exact extractionTermNegationSetupTemplate_run
  · apply fixedNodeProgramTemplate_run
    · simp [extractionTermNodeRegisters,NodePrinterRegisters.Valid]
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst t
      simp [symbolicAssignmentTemplate,FixedNodeTemplate.ops,nodeFieldOperations,
        GeneratorOperation.Valid,AffineAtom.Valid,extractionTermNodeRegisters]

end ShiReversibleGenerator
