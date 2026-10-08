import ReversibleTickResourcePreludeMetadata
import ReversibleProgramTemplateList
import ReversibleCounterAffineProgramTemplates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

noncomputable def tickMetadataHandoffPrograms (tm : Turing.FinTM2) :
    List (CounterProgramTemplate (FixedLeafRegister (tickTraversalSupply tm))) :=
  [counterAffineCopyProgramTemplate (.inl 0) (tickTraversalSpare tm 6) (.inl 5) 0 1 0,
   counterAffineCopyProgramTemplate (.inl 1) (tickTraversalSpare tm 7) (.inl 5) 0 1 0,
   counterAffineCopyProgramTemplate (.inl 11) (tickTraversalSpare tm 1) (.inl 5) 0 1 0,
   counterAffineCopyProgramTemplate (.inl 2) (.inl 1) (.inl 5) 0 1 0,
   cleanupProgramTemplate [.inl 3,.inl 4,.inl 10,.inl 11,.inl 9]]

/-- Save time before replacing control1 by capacity, and history end before clearing control11. -/
noncomputable def tickMetadataHandoffTemplate (tm : Turing.FinTM2) :=
  listProgramTemplate (tickMetadataHandoffPrograms tm)

theorem tickMetadataHandoffTemplate_embeds (tm : Turing.FinTM2) :
    (tickMetadataHandoffTemplate tm).Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  simp only [tickMetadataHandoffPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact cleanupProgramTemplate_embeds _

theorem tickMetadataHandoffTemplate_run (tm : Turing.FinTM2) :
    (tickMetadataHandoffTemplate tm).Runs := by
  apply listProgramTemplate_run
  · intro p hp
    simp only [tickMetadataHandoffPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    · exact cleanupProgramTemplate_embeds _
  · intro p hp
    simp only [tickMetadataHandoffPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl
    · apply counterAffineCopyProgramTemplate_run <;> simp [tickTraversalSpare]
    · apply counterAffineCopyProgramTemplate_run <;> simp [tickTraversalSpare]
    · apply counterAffineCopyProgramTemplate_run <;> simp [tickTraversalSpare]
    · apply counterAffineCopyProgramTemplate_run <;> simp
    · exact cleanupProgramTemplate_run _

theorem tickMetadataHandoffTemplate_ready (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickMetadataHandoffTemplate tm).ready cs ↔ cs (.inl 5)=0 := by
  simp [tickMetadataHandoffTemplate,tickMetadataHandoffPrograms,listProgramTemplate,identityProgramTemplate,
    sequenceProgramTemplate,counterAffineCopyProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply,tickTraversalSpare]

theorem tickMetadataHandoffTemplate_bytes (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    (tickMetadataHandoffTemplate tm).bytes cs=[] := rfl

theorem tickMetadataHandoffTemplate_metadata (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) :
    let final := (tickMetadataHandoffTemplate tm).counters cs
    final (tickTraversalSpare tm 6)=cs (.inl 0) ∧ final (tickTraversalSpare tm 7)=cs (.inl 1) ∧
      final (tickTraversalSpare tm 1)=cs (.inl 11) ∧ final (.inl 1)=cs (.inl 2) ∧
      final (.inl 0)=cs (.inl 0) ∧ final (.inl 9)=0 := by
  simp [tickMetadataHandoffTemplate,tickMetadataHandoffPrograms,listProgramTemplate,identityProgramTemplate,
    sequenceProgramTemplate,counterAffineCopyProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply,tickTraversalSpare]

theorem tickMetadataHandoffTemplate_scratch_ready (tm : Turing.FinTM2)
    (cs : FixedLeafRegister (tickTraversalSupply tm) → Nat) (h : cs (.inl 5)=0) :
    fixedGuardedEmitterReady (tickTraversalSupply tm) ((tickMetadataHandoffTemplate tm).counters cs) := by
  simp [fixedGuardedEmitterReady,tickMetadataHandoffTemplate,tickMetadataHandoffPrograms,listProgramTemplate,
    identityProgramTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,cleanupProgramTemplate,
    cleanupCounters_apply,tickTraversalSpare,h]

end ShiReversibleGenerator
