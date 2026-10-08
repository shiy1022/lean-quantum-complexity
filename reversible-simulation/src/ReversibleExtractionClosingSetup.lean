import ReversibleExtractionTermSizeResources
import ReversibleExtractionClosingCertificate
import ReversibleExtractionClosingPointerProgram

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Actual runtime arithmetic binds the current term-negation wire and the suffix root. -/
noncomputable def extractionClosingSetupTemplate (tm : Turing.FinTM2) :=
  sequenceProgramTemplate (extractionTermSizeProgramTemplate tm) extractionClosingPointerTemplate

theorem extractionClosingSetupTemplate_embeds (tm : Turing.FinTM2) :
    (extractionClosingSetupTemplate tm).Embeds :=
  sequenceProgramTemplate_embeds _ _ (extractionTermSizeProgramTemplate_embeds tm)
    extractionClosingPointerTemplate_embeds

theorem extractionClosingSetupTemplate_run (tm : Turing.FinTM2) :
    (extractionClosingSetupTemplate tm).Runs :=
  sequenceProgramTemplate_run _ _ (extractionTermSizeProgramTemplate_embeds tm)
    (extractionTermSizeProgramTemplate_run tm) extractionClosingPointerTemplate_run

end ShiReversibleGenerator
