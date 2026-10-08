import ReversibleExtractionForestRegisterInjection
import ReversibleCounterAffineOffsetCopyBudget
import ReversibleCounterPairRetreatBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Descending output emission retreats one padded slot before printing its original formula. -/
noncomputable def extractionForestRetreatPrograms : List (CounterProgramTemplate ExtractionForestRegister) :=
  [cleanupProgramTemplate [7],counterAffineCopyProgramTemplate 27 8 7 1 1 0,counterPairRetreatTemplate 18 25 8]

noncomputable def extractionForestRetreatTemplate := listProgramTemplate extractionForestRetreatPrograms

theorem extractionForestRetreatTemplate_embeds : extractionForestRetreatTemplate.Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  simp only [extractionForestRetreatPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact cleanupProgramTemplate_embeds _
  · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
  · exact counterPairRetreatTemplate_embeds _ _ _

theorem extractionForestRetreatTemplate_run : extractionForestRetreatTemplate.Runs := by
  apply listProgramTemplate_run
  · intro p hp
    simp only [extractionForestRetreatPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact cleanupProgramTemplate_embeds _
    · exact counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _
    · exact counterPairRetreatTemplate_embeds _ _ _
  · intro p hp
    simp only [extractionForestRetreatPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact cleanupProgramTemplate_run _
    · exact counterAffineCopyProgramTemplate_run _ _ _ _ _ _ (by decide) (by decide) (by decide)
    · exact counterPairRetreatTemplate_run _ _ _

theorem extractionForestRetreatTemplate_ready (cs : ExtractionForestRegister → Nat) :
    extractionForestRetreatTemplate.ready cs := by
  refine ⟨trivial,?_,?_,trivial⟩
  · simp [counterAffineCopyProgramTemplate,cleanupProgramTemplate,cleanupCounters_apply]
  · exact counterPairRetreatTemplate_ready _ _ _ (by decide) (by decide) _

theorem extractionForestRetreatTemplate_bytes (cs : ExtractionForestRegister → Nat) :
    extractionForestRetreatTemplate.bytes cs=[] := by
  simp [extractionForestRetreatTemplate,extractionForestRetreatPrograms,listProgramTemplate,
    sequenceProgramTemplate,identityProgramTemplate,cleanupProgramTemplate,counterAffineCopyProgramTemplate,
    counterPairRetreatTemplate_bytes]

theorem extractionForestRetreatTemplate_counters (cs : ExtractionForestRegister → Nat) :
    extractionForestRetreatTemplate.counters cs=Function.update (Function.update (Function.update
      (cleanupCounters [7] cs) 18 (cs 18-(cs 27+1))) 25 (cs 25-(cs 27+1))) 8 0 := by
  change (counterPairRetreatTemplate (18 : ExtractionForestRegister) 25 8).counters
    ((counterAffineCopyProgramTemplate 27 8 7 1 1 0).counters ((cleanupProgramTemplate [7]).counters cs))=_
  rw [counterPairRetreatTemplate_counters _ _ _ (by decide) (by decide) (by decide)]
  funext q
  simp only [counterAffineCopyProgramTemplate,cleanupProgramTemplate,Function.update_apply,cleanupCounters_apply]
  split_ifs <;> simp_all <;> omega

theorem extractionForestRetreatTemplate_resources (bound : Polynomial Nat) :
    extractionForestRetreatTemplate.CounterBound bound ∧ extractionForestRetreatTemplate.PolynomiallyTimed bound := by
  apply listProgramTemplate_polynomial_certificate
  · intro p hp b
    simp only [extractionForestRetreatPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact cleanupProgramTemplate_polynomial _ b
    · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ b
    · exact counterPairRetreatTemplate_polynomial _ _ _ b
  · intro p hp b
    simp only [extractionForestRetreatPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨b,by intro n cs hb q; exact cleanupCounters_uniform_bound _ cs _ hb q⟩
    · exact counterAffineOffsetCopyProgramTemplate_budget _ _ _ _ _ b
    · exact ⟨b,by intro n cs hb q; exact counterPairRetreatTemplate_budget _ _ _ (by decide) (by decide) (by decide) cs (b.eval n) hb q⟩

end ShiReversibleGenerator
