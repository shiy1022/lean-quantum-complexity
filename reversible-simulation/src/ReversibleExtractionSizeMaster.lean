import ReversibleExtractionSizeSetup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

noncomputable def extractionSizeMasterTemplate (tm : Turing.FinTM2) : CounterProgramTemplate ExtractionSizeRegister :=
  sequenceProgramTemplate extractionSizeSetupTemplate (extractionSizeLoopTemplate tm)

theorem extractionSizeMasterTemplate_embeds (tm : Turing.FinTM2) : (extractionSizeMasterTemplate tm).Embeds :=
  sequenceProgramTemplate_embeds _ _ extractionSizeSetupTemplate_embeds (extractionSizeLoopTemplate_embeds tm)

theorem extractionSizeMasterTemplate_run (tm : Turing.FinTM2) : (extractionSizeMasterTemplate tm).Runs :=
  sequenceProgramTemplate_run _ _ extractionSizeSetupTemplate_embeds extractionSizeSetupTemplate_run
    (extractionSizeLoopTemplate_run tm)

theorem extractionSizeMasterTemplate_ready (tm : Turing.FinTM2) (cs : ExtractionSizeRegister → Nat) :
    (extractionSizeMasterTemplate tm).ready cs := by
  refine ⟨extractionSizeSetupTemplate_ready cs,?_⟩
  apply extractionSizeLoopTemplate_ready <;> rw [extractionSizeSetupTemplate_counters] <;>
    simp [cleanupCounters_apply]

theorem extractionSizeMasterTemplate_polynomial (tm : Turing.FinTM2) (bound : Polynomial Nat) :
    (extractionSizeMasterTemplate tm).PolynomiallyTimed bound :=
  sequenceProgramTemplate_polynomial _ _ bound (bound+Polynomial.C 1)
    (extractionSizeSetupTemplate_polynomial bound)
    (by intro n cs hb hr q; simpa only [Polynomial.eval_add,Polynomial.eval_C] using
      extractionSizeSetupTemplate_uniform_bound cs (bound.eval n) hb q)
    (extractionSizeLoopTemplate_polynomial tm (bound+Polynomial.C 1))

/-- The actual finite setup and size traversal compute the exact output formula size. -/
theorem extractionSizeMasterTemplate_result (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (cs : ExtractionSizeRegister → Nat) :
    (extractionSizeMasterTemplate tm).counters cs 4=(extractionFormula tm e (cs 0) (cs 1)).size ∧
      (extractionSizeMasterTemplate tm).counters cs 2=0 := by
  change (extractionSizeLoopTemplate tm).counters (extractionSizeSetupTemplate.counters cs) 4=_ ∧ _
  have h2 : extractionSizeSetupTemplate.counters cs 2=cs 0+1 := by
    rw [extractionSizeSetupTemplate_counters]; simp [cleanupCounters_apply]
  have h4 : extractionSizeSetupTemplate.counters cs 4=1 := by
    rw [extractionSizeSetupTemplate_counters]; simp
  have h1 : extractionSizeSetupTemplate.counters cs 1=cs 1 := by
    rw [extractionSizeSetupTemplate_counters]; simp [cleanupCounters_apply]
  refine ⟨?_,(extractionSizeLoopTemplate_result tm (extractionSizeSetupTemplate.counters cs)).2.2⟩
  simpa only [h1] using extractionSizeLoopTemplate_formula_size tm e _ (cs 0) h2 h4

end ShiReversibleGenerator
