import ReversibleResourceHeaderPrelude
import ReversibleCounterAffineExitBounds
import ReversibleDecrementProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

abbrev ResourceHeaderRegister := RawLengthPhaseRegister WorkspaceRegister

noncomputable def resourceHeaderAdministrationPrograms : List (CounterProgramTemplate ResourceHeaderRegister) :=
  [counterAffineCopyProgramTemplate (.inr 7) (.inr 12) (.inr 5) 0 1 0,
    counterAffineAccumulationProgramTemplate ⟨.inr 9,.inr 12,0,1⟩ (.inr 5),
    decrementProgramTemplate (.inr 12),
    counterAffineCopyProgramTemplate (.inl 1) (.inr 13) (.inr 5) 0 1 0]

/-- The actual ancilla convention and layer-count header fields are computed by fixed finite arithmetic. -/
noncomputable def resourceHeaderAdministrationTemplate : CounterProgramTemplate ResourceHeaderRegister :=
  listProgramTemplate resourceHeaderAdministrationPrograms

theorem resourceHeaderAdministrationTemplate_embeds : resourceHeaderAdministrationTemplate.Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  simp only [resourceHeaderAdministrationPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact counterAffineAccumulationProgramTemplate_embeds _ _
  · exact decrementProgramTemplate_embeds _
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _

theorem resourceHeaderAdministrationTemplate_run : resourceHeaderAdministrationTemplate.Runs := by
  apply listProgramTemplate_run
  · intro p hp
    simp only [resourceHeaderAdministrationPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    · exact counterAffineAccumulationProgramTemplate_embeds _ _
    · exact decrementProgramTemplate_embeds _
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · intro p hp
    simp only [resourceHeaderAdministrationPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · apply counterAffineCopyProgramTemplate_run <;> simp
    · apply counterAffineAccumulationProgramTemplate_run <;> simp [AffineAtom.Valid]
    · exact decrementProgramTemplate_run _
    · apply counterAffineCopyProgramTemplate_run <;> simp

theorem resourceHeaderAdministrationTemplate_ready (cs : ResourceHeaderRegister → Nat) :
    resourceHeaderAdministrationTemplate.ready cs ↔ cs (.inr 5)=0 := by
  simp [resourceHeaderAdministrationTemplate,resourceHeaderAdministrationPrograms,listProgramTemplate,
    sequenceProgramTemplate,identityProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.apply,decrementProgramTemplate]

theorem resourceHeaderAdministrationTemplate_bytes (cs : ResourceHeaderRegister → Nat) :
    resourceHeaderAdministrationTemplate.bytes cs=[] := by
  simp [resourceHeaderAdministrationTemplate,resourceHeaderAdministrationPrograms,listProgramTemplate,
    sequenceProgramTemplate,identityProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,decrementProgramTemplate]

theorem resourceHeaderAdministrationTemplate_counters (cs : ResourceHeaderRegister → Nat) :
    resourceHeaderAdministrationTemplate.counters cs=
      Function.update (Function.update cs (.inr 12) (cs (.inr 7)+cs (.inr 9)-1)) (.inr 13) (cs (.inl 1)) := by
  funext q
  cases q with
  | inl j =>
    fin_cases j <;> simp [resourceHeaderAdministrationTemplate,resourceHeaderAdministrationPrograms,listProgramTemplate,
      sequenceProgramTemplate,identityProgramTemplate,counterAffineCopyProgramTemplate,
      counterAffineAccumulationProgramTemplate,AffineAtom.apply,decrementProgramTemplate]
  | inr j =>
    fin_cases j <;> simp [resourceHeaderAdministrationTemplate,resourceHeaderAdministrationPrograms,listProgramTemplate,
      sequenceProgramTemplate,identityProgramTemplate,counterAffineCopyProgramTemplate,
      counterAffineAccumulationProgramTemplate,AffineAtom.apply,decrementProgramTemplate]

end ShiReversibleGenerator
