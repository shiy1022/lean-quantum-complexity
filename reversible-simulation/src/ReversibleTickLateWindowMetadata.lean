import ReversibleTickLateWindowFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickLateWindowTemplate_raw_length (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickLateWindowTemplate tm bound).counters cs (tickTraversalSpare tm 6)=cs (tickTraversalSpare tm 6) := by
  simp [tickLateWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    tickWindowRetreatTemplate_counters,tickInputRetreatTemplate_counters,tickTraversalSpare]

theorem tickLateWindowTemplate_time (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickLateWindowTemplate tm bound).counters cs (tickTraversalSpare tm 7)=cs (tickTraversalSpare tm 7) := by
  simp [tickLateWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    tickWindowRetreatTemplate_counters,tickInputRetreatTemplate_counters,tickTraversalSpare]

end ShiReversibleGenerator
