import ReversibleOutputCopyStridedLayers
import ReversibleTemplateRegisterInjectionRun
import ReversibleWorkspaceOffsets
import ReversibleProgramTemplateList

set_option autoImplicit false
namespace ShiReversibleGenerator

abbrev OutputCopyMasterRegister := WorkspaceRegister ⊕ OutputCopyRegister

noncomputable def outputCopySetupPrograms : List (CounterProgramTemplate OutputCopyMasterRegister) :=
  [counterAffineCopyProgramTemplate (.inl 10) (.inr 0) (.inl 5) 0 1 1,
   counterAffineCopyProgramTemplate (.inl 10) (.inr 1) (.inl 5) 0 1 0,
   counterAffineAccumulationProgramTemplate ⟨.inl 9,.inr 1,0,1⟩ (.inl 5),
   decrementProgramTemplate (.inr 1),
   counterAffineCopyProgramTemplate (.inl 4) (.inr 5) (.inl 5) 0 1 0,
   counterAffineCopyProgramTemplate (.inl 9) (.inr 6) (.inl 5) 0 1 0,
   cleanupProgramTemplate [.inr 2,.inr 3,.inr 4,.inr 7,.inr 8,.inr 9]]

/-- Runtime metadata seeds the last extraction root, last output wire, stride and loop count. -/
noncomputable def outputCopySetupTemplate := listProgramTemplate outputCopySetupPrograms

theorem outputCopySetupTemplate_embeds : outputCopySetupTemplate.Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  simp only [outputCopySetupPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact counterAffineAccumulationProgramTemplate_embeds _ _
  · exact decrementProgramTemplate_embeds _
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact cleanupProgramTemplate_embeds _

theorem outputCopySetupTemplate_run : outputCopySetupTemplate.Runs := by
  apply listProgramTemplate_run
  · intro p hp
    simp only [outputCopySetupPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    · exact counterAffineAccumulationProgramTemplate_embeds _ _
    · exact decrementProgramTemplate_embeds _
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    · exact cleanupProgramTemplate_embeds _
  · intro p hp
    simp only [outputCopySetupPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · apply counterAffineCopyProgramTemplate_run <;> simp
    · apply counterAffineCopyProgramTemplate_run <;> simp
    · apply counterAffineAccumulationProgramTemplate_run
      simp [AffineAtom.Valid]
    · exact decrementProgramTemplate_run _
    · apply counterAffineCopyProgramTemplate_run <;> simp
    · apply counterAffineCopyProgramTemplate_run <;> simp
    · exact cleanupProgramTemplate_run _

end ShiReversibleGenerator
