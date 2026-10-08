import ReversibleTickRetreatHistoryCircuitCertificate
import ReversibleTickInitializedWindowTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Emit the later slices, reset the clamped boundary pointers, then prepend the initialized tick. -/
noncomputable def tickForwardHistoryTemplate (tm : Turing.FinTM2) (bound : Nat) :=
  sequenceProgramTemplate (tickRetreatIterationTemplate tm bound)
    (sequenceProgramTemplate (tickInitializedWindowTemplate tm) (tickForestTemplate tm 18 bound false))

theorem tickForwardHistoryTemplate_embeds (tm : Turing.FinTM2) (bound : Nat) :
    (tickForwardHistoryTemplate tm bound).Embeds :=
  sequenceProgramTemplate_embeds _ _ (tickRetreatIterationTemplate_embeds tm bound)
    (sequenceProgramTemplate_embeds _ _ (tickInitializedWindowTemplate_embeds tm)
      (tickForestTemplate_embeds tm 18 bound false))

theorem tickForwardHistoryTemplate_run (tm : Turing.FinTM2) (bound : Nat) :
    (tickForwardHistoryTemplate tm bound).Runs :=
  sequenceProgramTemplate_run _ _ (tickRetreatIterationTemplate_embeds tm bound)
    (tickRetreatIterationTemplate_run tm bound)
    (sequenceProgramTemplate_run _ _ (tickInitializedWindowTemplate_embeds tm)
      (tickInitializedWindowTemplate_run tm) (tickForestTemplate_run tm 18 bound false))

theorem tickRetreatIterationTemplate_spare_frame (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (j : Fin 8)
    (h0 : j ≠ 0) (h2 : j ≠ 2) (h3 : j ≠ 3) (h4 : j ≠ 4) :
    (tickRetreatIterationTemplate tm bound).counters cs (tickTraversalSpare tm j)=cs (tickTraversalSpare tm j) := by
  apply descendingProgramTemplate_point_frame
  · exact fun h => h3 (tickTraversalSpare_injective tm h)
  · intro t
    exact tickRetreatStepTemplate_spare_frame tm (bound+1) bound t j h0 h2 h4

end ShiReversibleGenerator
