import ReversibleTickInputRetreat
import ReversibleTickInverseHistoryTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Spare1 retains the prepared history end; seed the last output and its padded source. -/
noncomputable def tickLateWindowTemplate (tm : Turing.FinTM2) (bound : Nat) :=
  sequenceProgramTemplate
    (counterAffineCopyProgramTemplate (tickTraversalSpare tm 1) (.inl 0) (.inl 5) bound 1 0)
    (sequenceProgramTemplate
      (counterAffineCopyProgramTemplate (tickTraversalSpare tm 1) (tickTraversalSpare tm 2) (.inl 5) 0 1 0)
      (sequenceProgramTemplate (tickWindowRetreatTemplate tm bound) (tickInputRetreatTemplate tm bound)))

theorem tickLateWindowTemplate_embeds (tm : Turing.FinTM2) (bound : Nat) :
    (tickLateWindowTemplate tm bound).Embeds :=
  sequenceProgramTemplate_embeds _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
    (sequenceProgramTemplate_embeds _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
      (sequenceProgramTemplate_embeds _ _ (tickWindowRetreatTemplate_embeds tm bound)
        (tickInputRetreatTemplate_embeds tm bound)))

theorem tickLateWindowTemplate_run (tm : Turing.FinTM2) (bound : Nat) :
    (tickLateWindowTemplate tm bound).Runs := by
  apply sequenceProgramTemplate_run
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · apply counterAffineCopyProgramTemplate_run <;> simp [tickTraversalSpare]
  · apply sequenceProgramTemplate_run
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    · apply counterAffineCopyProgramTemplate_run
      · exact fun h => (by decide : (1 : Fin 8) ≠ 2) (tickTraversalSpare_injective tm h)
      · simp [tickTraversalSpare]
      · simp [tickTraversalSpare]
    · exact sequenceProgramTemplate_run _ _ (tickWindowRetreatTemplate_embeds tm bound)
        (tickWindowRetreatTemplate_run tm bound) (tickInputRetreatTemplate_run tm bound)

theorem tickLateWindowTemplate_bytes (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickLateWindowTemplate tm bound).bytes cs=[] := by
  simp only [tickLateWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    tickWindowRetreatTemplate_bytes,tickInputRetreatTemplate_bytes,List.append_nil]

theorem tickLateWindowTemplate_input (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickLateWindowTemplate tm bound).counters cs (.inl 0)=
      (cs (tickTraversalSpare tm 1)+bound)-2*(configurationWidth tm (cs (.inl 1))*(bound+1)) := by
  simp [tickLateWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    tickWindowRetreatTemplate_counters,tickInputRetreatTemplate_counters,tickTraversalSpare,Nat.sub_sub]
  congr 1
  omega

theorem tickLateWindowTemplate_output (tm : Turing.FinTM2) (bound : Nat)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickLateWindowTemplate tm bound).counters cs (tickTraversalSpare tm 2)=
      cs (tickTraversalSpare tm 1)-configurationWidth tm (cs (.inl 1))*(bound+1) := by
  simp [tickLateWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    tickWindowRetreatTemplate_counters,tickInputRetreatTemplate_counters,tickTraversalSpare]

end ShiReversibleGenerator
