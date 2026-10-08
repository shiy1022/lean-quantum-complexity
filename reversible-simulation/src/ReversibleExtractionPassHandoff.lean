import ReversibleExtractionTraversalRegisterInjection
import ReversibleCounterAffineOffsetCopyBudget
import ReversibleCleanupProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Both descending term passes restart length at capacity and consume capacity-plus-one terms. -/
noncomputable def extractionDescendingPassHandoffPrograms : List (CounterProgramTemplate ExtractionTraversalRegister) :=
  [cleanupProgramTemplate [7],counterAffineCopyProgramTemplate 0 2 7 0 1 0,
    counterAffineCopyProgramTemplate 0 22 7 1 1 0]

noncomputable def extractionDescendingPassHandoffTemplate := listProgramTemplate extractionDescendingPassHandoffPrograms

/-- After inverse prefix, the false base supplies the first closing endpoint three wires later. -/
noncomputable def extractionInverseClosingHandoffTemplate :=
  sequenceProgramTemplate extractionDescendingPassHandoffTemplate
    (counterAffineCopyProgramTemplate 18 20 7 3 1 0)

theorem extractionDescendingPassHandoffTemplate_embeds : extractionDescendingPassHandoffTemplate.Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  simp only [extractionDescendingPassHandoffPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact cleanupProgramTemplate_embeds _
  all_goals exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _

theorem extractionDescendingPassHandoffTemplate_run : extractionDescendingPassHandoffTemplate.Runs := by
  apply listProgramTemplate_run
  · intro p hp
    simp only [extractionDescendingPassHandoffPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact cleanupProgramTemplate_embeds _
    all_goals exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · intro p hp
    simp only [extractionDescendingPassHandoffPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact cleanupProgramTemplate_run _
    all_goals exact counterAffineCopyProgramTemplate_run _ _ _ _ _ _ (by decide) (by decide) (by decide)

theorem extractionDescendingPassHandoffTemplate_counters (cs : ExtractionTraversalRegister → Nat) :
    extractionDescendingPassHandoffTemplate.counters cs=
      Function.update (Function.update (cleanupCounters [7] cs) 2 (cs 0)) 22 (cs 0+1) := by
  simp [extractionDescendingPassHandoffTemplate,extractionDescendingPassHandoffPrograms,
    listProgramTemplate,sequenceProgramTemplate,identityProgramTemplate,counterAffineCopyProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply]

theorem extractionDescendingPassHandoffTemplate_ready (cs : ExtractionTraversalRegister → Nat) :
    extractionDescendingPassHandoffTemplate.ready cs := by
  simp [extractionDescendingPassHandoffTemplate,extractionDescendingPassHandoffPrograms,
    listProgramTemplate,sequenceProgramTemplate,identityProgramTemplate,counterAffineCopyProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply]

theorem extractionDescendingPassHandoffTemplate_bytes (cs : ExtractionTraversalRegister → Nat) :
    extractionDescendingPassHandoffTemplate.bytes cs=[] := by
  simp [extractionDescendingPassHandoffTemplate,extractionDescendingPassHandoffPrograms,
    listProgramTemplate,sequenceProgramTemplate,identityProgramTemplate,counterAffineCopyProgramTemplate,cleanupProgramTemplate]

theorem extractionDescendingPassHandoffTemplate_resources (bound : Polynomial Nat) :
    extractionDescendingPassHandoffTemplate.CounterBound bound ∧
      extractionDescendingPassHandoffTemplate.PolynomiallyTimed bound := by
  apply listProgramTemplate_polynomial_certificate
  · intro p hp b
    simp only [extractionDescendingPassHandoffPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact cleanupProgramTemplate_polynomial _ b
    all_goals exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ b
  · intro p hp b
    simp only [extractionDescendingPassHandoffPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨b,by intro n cs hb q; exact cleanupCounters_uniform_bound _ cs _ hb q⟩
    all_goals exact counterAffineOffsetCopyProgramTemplate_budget _ _ _ _ _ b

end ShiReversibleGenerator
