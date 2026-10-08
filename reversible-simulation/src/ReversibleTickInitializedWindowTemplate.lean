import ReversibleTickForwardIterationCircuitCertificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- Spare6 retains raw length; the initialized configuration has stride18 and result offset17. -/
noncomputable def tickInitializedWindowAtom (tm : Turing.FinTM2) :
    AffineAtom (FixedLeafRegister (tickTraversalSupply tm)) :=
  ⟨.inl 1,tickTraversalSpare tm 2,18*tickWidthOffset tm,18*tickWidthSlope tm⟩

noncomputable def tickInitializedWindowTemplate (tm : Turing.FinTM2) :=
  sequenceProgramTemplate
    (counterAffineCopyProgramTemplate (tickTraversalSpare tm 6) (.inl 0) (.inl 5) 17 1 0)
    (sequenceProgramTemplate
      (counterAffineCopyProgramTemplate (tickTraversalSpare tm 6) (tickTraversalSpare tm 2) (.inl 5) 0 1 0)
      (counterAffineAccumulationProgramTemplate (tickInitializedWindowAtom tm) (.inl 5)))

theorem tickInitializedWindowTemplate_embeds (tm : Turing.FinTM2) :
    (tickInitializedWindowTemplate tm).Embeds :=
  sequenceProgramTemplate_embeds _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
    (sequenceProgramTemplate_embeds _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
      (counterAffineAccumulationProgramTemplate_embeds _ _))

theorem tickInitializedWindowTemplate_run (tm : Turing.FinTM2) :
    (tickInitializedWindowTemplate tm).Runs := by
  apply sequenceProgramTemplate_run
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · apply counterAffineCopyProgramTemplate_run <;> simp [tickTraversalSpare]
  · apply sequenceProgramTemplate_run
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    · apply counterAffineCopyProgramTemplate_run
      · exact fun h => (by decide : (6 : Fin 8) ≠ 2) (tickTraversalSpare_injective tm h)
      · simp [tickTraversalSpare]
      · simp [tickTraversalSpare]
    · apply counterAffineAccumulationProgramTemplate_run
      simp [AffineAtom.Valid,tickInitializedWindowAtom,tickTraversalSpare]

theorem tickInitializedWindowTemplate_ready (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickInitializedWindowTemplate tm).ready cs ↔ cs (.inl 5)=0 := by
  simp [tickInitializedWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,tickTraversalSpare]

theorem tickInitializedWindowTemplate_input (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickInitializedWindowTemplate tm).counters cs (.inl 0)=cs (tickTraversalSpare tm 6)+17 := by
  simp [tickInitializedWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.apply,tickInitializedWindowAtom,tickTraversalSpare]

theorem tickInitializedWindowTemplate_output (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickInitializedWindowTemplate tm).counters cs (tickTraversalSpare tm 2)=
      cs (tickTraversalSpare tm 6)+18*configurationWidth tm (cs (.inl 1)) := by
  rw [tickWidth_affine]
  simp [tickInitializedWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.apply,tickInitializedWindowAtom,tickTraversalSpare]
  ring

theorem tickInitializedWindowTemplate_control_frame (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (q : Fin 14) (hq : q ≠ 0) :
    (tickInitializedWindowTemplate tm).counters cs (.inl q)=cs (.inl q) := by
  simp [tickInitializedWindowTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.apply,tickInitializedWindowAtom,tickTraversalSpare,hq]

theorem tickInitializedWindowTemplate_bytes (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickInitializedWindowTemplate tm).bytes cs=[] := rfl

end ShiReversibleGenerator
