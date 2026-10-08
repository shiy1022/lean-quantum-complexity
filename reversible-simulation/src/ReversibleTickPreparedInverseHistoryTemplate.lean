import ReversibleTickResourceInverseWireCertificate
import ReversibleTickInitializedWindowClock

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The inverse history printer seeds its initialized input/output pointers before printing. -/
noncomputable def tickPreparedInverseHistoryTemplate (tm : Turing.FinTM2) :=
  sequenceProgramTemplate (tickInitializedWindowTemplate tm)
    (tickInverseHistoryTemplate tm (tickSizeBound tm))

theorem tickPreparedInverseHistoryTemplate_embeds (tm : Turing.FinTM2) :
    (tickPreparedInverseHistoryTemplate tm).Embeds :=
  sequenceProgramTemplate_embeds _ _ (tickInitializedWindowTemplate_embeds tm)
    (tickInverseHistoryTemplate_embeds tm (tickSizeBound tm))

theorem tickPreparedInverseHistoryTemplate_run (tm : Turing.FinTM2) :
    (tickPreparedInverseHistoryTemplate tm).Runs :=
  sequenceProgramTemplate_run _ _ (tickInitializedWindowTemplate_embeds tm)
    (tickInitializedWindowTemplate_run tm)
    (tickInverseHistoryTemplate_run tm (tickSizeBound tm))

noncomputable def tickHandoffInverseTemplate (tm : Turing.FinTM2) :=
  sequenceProgramTemplate (tickMetadataHandoffTemplate tm) (tickPreparedInverseHistoryTemplate tm)

theorem tickHandoffInverseTemplate_embeds (tm : Turing.FinTM2) :
    (tickHandoffInverseTemplate tm).Embeds :=
  sequenceProgramTemplate_embeds _ _ (tickMetadataHandoffTemplate_embeds tm)
    (tickPreparedInverseHistoryTemplate_embeds tm)

theorem tickHandoffInverseTemplate_run (tm : Turing.FinTM2) :
    (tickHandoffInverseTemplate tm).Runs :=
  sequenceProgramTemplate_run _ _ (tickMetadataHandoffTemplate_embeds tm)
    (tickMetadataHandoffTemplate_run tm) (tickPreparedInverseHistoryTemplate_run tm)

end ShiReversibleGenerator
