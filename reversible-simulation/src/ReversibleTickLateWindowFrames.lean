import ReversibleTickLateWindowTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickLateWindowTemplate_ready (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickLateWindowTemplate tm bound).ready cs ↔ cs (.inl 5)=0 := by
  simp [tickLateWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    tickWindowRetreatTemplate_ready,tickInputRetreatTemplate_ready,tickWindowRetreatTemplate_counters,
    tickTraversalSpare]

theorem tickLateWindowTemplate_control_frame (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (q : Fin 14) (hq : q ≠ 0) :
    (tickLateWindowTemplate tm bound).counters cs (.inl q)=cs (.inl q) := by
  simp [tickLateWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    tickWindowRetreatTemplate_counters,tickInputRetreatTemplate_counters,tickTraversalSpare,hq]

theorem tickLateWindowTemplate_remaining (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickLateWindowTemplate tm bound).counters cs (tickTraversalSpare tm 3)=cs (tickTraversalSpare tm 3) := by
  simp [tickLateWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    tickWindowRetreatTemplate_counters,tickInputRetreatTemplate_counters,tickTraversalSpare]

theorem tickLateWindowTemplate_prepared_end (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickLateWindowTemplate tm bound).counters cs (tickTraversalSpare tm 1)=cs (tickTraversalSpare tm 1) := by
  simp [tickLateWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    tickWindowRetreatTemplate_counters,tickInputRetreatTemplate_counters,tickTraversalSpare]

end ShiReversibleGenerator
