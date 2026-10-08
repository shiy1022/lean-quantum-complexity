import ReversibleExtractionSizeLoopClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Initialize the suffix pass from runtime capacity and output position, clearing its actual scratch. -/
noncomputable def extractionSizeSetupTemplate : CounterProgramTemplate ExtractionSizeRegister :=
  sequenceProgramTemplate (cleanupProgramTemplate [3,5,6,7])
    (sequenceProgramTemplate (counterAffineCopyProgramTemplate 0 2 7 1 1 0)
      (counterAffineCopyProgramTemplate 0 4 7 1 0 0))

theorem extractionSizeSetupTemplate_embeds : extractionSizeSetupTemplate.Embeds :=
  sequenceProgramTemplate_embeds _ _ (cleanupProgramTemplate_embeds _)
    (sequenceProgramTemplate_embeds _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
      (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _))

theorem extractionSizeSetupTemplate_run : extractionSizeSetupTemplate.Runs :=
  sequenceProgramTemplate_run _ _ (cleanupProgramTemplate_embeds _) (cleanupProgramTemplate_run _)
    (sequenceProgramTemplate_run _ _ (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)
      (counterAffineCopyProgramTemplate_run _ _ _ _ _ _ (by decide) (by decide) (by decide))
      (counterAffineCopyProgramTemplate_run _ _ _ _ _ _ (by decide) (by decide) (by decide)))

theorem extractionSizeSetupTemplate_ready (cs : ExtractionSizeRegister → Nat) :
    extractionSizeSetupTemplate.ready cs := by
  simp [extractionSizeSetupTemplate,sequenceProgramTemplate,cleanupProgramTemplate,
    counterAffineCopyProgramTemplate,cleanupCounters_apply]

/-- The exact actual setup endpoint, with no scratch or size premise supplied by the caller. -/
theorem extractionSizeSetupTemplate_counters (cs : ExtractionSizeRegister → Nat) :
    extractionSizeSetupTemplate.counters cs=
      Function.update (Function.update (cleanupCounters [3,5,6,7] cs) 2 (cs 0+1)) 4 1 := by
  simp [extractionSizeSetupTemplate,sequenceProgramTemplate,cleanupProgramTemplate,
    counterAffineCopyProgramTemplate,cleanupCounters_apply]

theorem extractionSizeSetupTemplate_bytes (cs : ExtractionSizeRegister → Nat) :
    extractionSizeSetupTemplate.bytes cs=[] := rfl

theorem extractionSizeSetupTemplate_uniform_bound (cs : ExtractionSizeRegister → Nat) (B : Nat)
    (hb : ∀ q,cs q ≤ B) : ∀ q,extractionSizeSetupTemplate.counters cs q ≤ B+1 := by
  intro q
  rw [extractionSizeSetupTemplate_counters]
  by_cases h4 : q=4
  · subst q; simp
  by_cases h2 : q=2
  · subst q; simp; exact hb 0
  simp only [Function.update_of_ne h4,Function.update_of_ne h2,cleanupCounters_apply]
  have hq := hb q
  split <;> omega

theorem extractionSizeSetupTemplate_polynomial (bound : Polynomial Nat) :
    extractionSizeSetupTemplate.PolynomiallyTimed bound := by
  refine ⟨Polynomial.C 20*bound+Polynomial.C 20,?_⟩
  intro n cs hb hr
  have h0 := hb 0
  have h2 := hb 2
  have h3 := hb 3
  have h4 := hb 4
  have h5 := hb 5
  have h6 := hb 6
  have h7 := hb 7
  simp [extractionSizeSetupTemplate,sequenceProgramTemplate,cleanupProgramTemplate,
    counterAffineCopyProgramTemplate,cleanupSteps,cleanupCounters_apply,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  omega

end ShiReversibleGenerator
