import ReversibleTickForwardHistoryTemplate
import ReversibleTickLateWindowFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The finite forward emitter copies time-minus1, seeds late pointers and emits the entire history. -/
noncomputable def tickPreparedForwardHistoryTemplate (tm : Turing.FinTM2) (bound : Nat) :=
  sequenceProgramTemplate (tickHistoryCountTemplate tm)
    (sequenceProgramTemplate (tickLateWindowTemplate tm bound) (tickForwardHistoryTemplate tm bound))

theorem tickPreparedForwardHistoryTemplate_embeds (tm : Turing.FinTM2) (bound : Nat) :
    (tickPreparedForwardHistoryTemplate tm bound).Embeds :=
  sequenceProgramTemplate_embeds _ _ (tickHistoryCountTemplate_embeds tm)
    (sequenceProgramTemplate_embeds _ _ (tickLateWindowTemplate_embeds tm bound)
      (tickForwardHistoryTemplate_embeds tm bound))

theorem tickPreparedForwardHistoryTemplate_run (tm : Turing.FinTM2) (bound : Nat) :
    (tickPreparedForwardHistoryTemplate tm bound).Runs :=
  sequenceProgramTemplate_run _ _ (tickHistoryCountTemplate_embeds tm) (tickHistoryCountTemplate_run tm)
    (sequenceProgramTemplate_run _ _ (tickLateWindowTemplate_embeds tm bound)
      (tickLateWindowTemplate_run tm bound) (tickForwardHistoryTemplate_run tm bound))

end ShiReversibleGenerator
