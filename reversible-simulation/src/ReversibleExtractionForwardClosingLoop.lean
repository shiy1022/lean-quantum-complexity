import ReversibleExtractionClosingStep
import ReversibleDescendingProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- The actual forward closing pass consumes counter9 while the real step increments length2. -/
noncomputable def extractionForwardClosingLoopTemplate (tm : Turing.FinTM2) :=
  descendingProgramTemplate (extractionClosingStepTemplate tm false) 9

theorem extractionForwardClosingLoopTemplate_embeds (tm : Turing.FinTM2) :
    (extractionForwardClosingLoopTemplate tm).Embeds :=
  descendingProgramTemplate_embeds _ _ (extractionClosingStepTemplate_embeds tm false)

theorem extractionForwardClosingLoopTemplate_run (tm : Turing.FinTM2) :
    (extractionForwardClosingLoopTemplate tm).Runs :=
  descendingProgramTemplate_run _ _ (extractionClosingStepTemplate_embeds tm false)
    (extractionClosingStepTemplate_run tm false)

end ShiReversibleGenerator
