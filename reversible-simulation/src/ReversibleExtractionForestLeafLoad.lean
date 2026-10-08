import ReversibleExtractionForestRegisterInjection
import ReversibleCounterAffineOffsetCopyBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Restore the persistent runtime padding bound before the term printer reuses register4. -/
noncomputable def extractionForestLeafLoadTemplate : CounterProgramTemplate ExtractionForestRegister :=
  sequenceProgramTemplate (cleanupProgramTemplate [7]) (counterAffineCopyProgramTemplate 27 4 7 0 1 0)

theorem extractionForestLeafLoadTemplate_embeds : extractionForestLeafLoadTemplate.Embeds :=
  sequenceProgramTemplate_embeds _ _ (cleanupProgramTemplate_embeds _) (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)

theorem extractionForestLeafLoadTemplate_run : extractionForestLeafLoadTemplate.Runs :=
  sequenceProgramTemplate_run _ _ (cleanupProgramTemplate_embeds _) (cleanupProgramTemplate_run _)
    (counterAffineCopyProgramTemplate_run _ _ _ _ _ _ (by decide) (by decide) (by decide))

theorem extractionForestLeafLoadTemplate_counters (cs : ExtractionForestRegister → Nat) :
    extractionForestLeafLoadTemplate.counters cs=Function.update (cleanupCounters [7] cs) 4 (cs 27) := by
  simp [extractionForestLeafLoadTemplate,sequenceProgramTemplate,cleanupProgramTemplate,
    counterAffineCopyProgramTemplate,cleanupCounters_apply]

theorem extractionForestLeafLoadTemplate_ready (cs : ExtractionForestRegister → Nat) :
    extractionForestLeafLoadTemplate.ready cs := by
  simp [extractionForestLeafLoadTemplate,sequenceProgramTemplate,cleanupProgramTemplate,
    counterAffineCopyProgramTemplate,cleanupCounters_apply]

theorem extractionForestLeafLoadTemplate_bytes (cs : ExtractionForestRegister → Nat) :
    extractionForestLeafLoadTemplate.bytes cs=[] := rfl

theorem extractionForestLeafLoadTemplate_resources (bound : Polynomial Nat) :
    extractionForestLeafLoadTemplate.CounterBound bound ∧ extractionForestLeafLoadTemplate.PolynomiallyTimed bound := by
  refine ⟨⟨bound,?_⟩,?_⟩
  · intro n cs hb q
    rw [extractionForestLeafLoadTemplate_counters]
    simp only [Function.update_apply,cleanupCounters_apply]
    have hq := hb q
    have hs := hb 27
    split_ifs <;> omega
  · exact sequenceProgramTemplate_polynomial _ _ bound bound (cleanupProgramTemplate_polynomial _ bound)
      (fun n cs hb _ => cleanupCounters_uniform_bound _ cs _ hb)
      (counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ bound)

end ShiReversibleGenerator
