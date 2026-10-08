import ReversibleExtractionTermSizeProgram
import ReversibleInjectedTemplateCounterUpdates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

theorem extractionSizeStepTemplate_polynomial (tm : Turing.FinTM2) (bound : Polynomial Nat) :
    (extractionSizeStepTemplate tm).PolynomiallyTimed bound := by
  refine ⟨Polynomial.C 100*bound+Polynomial.C (100+Fintype.card (Option (MachineSymbol tm))*7),?_⟩
  intro n cs hb hr
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Nat.add_assoc] using
    extractionSizeStepTemplate_cost_bound tm cs (bound.eval n) (fun q _ => hb q) hr

theorem extractionTermSizeProgramTemplate_polynomial (tm : Turing.FinTM2) (bound : Polynomial Nat) :
    (extractionTermSizeProgramTemplate tm).PolynomiallyTimed bound := by
  apply sequenceProgramTemplate_polynomial _ _ bound bound
  · exact cleanupProgramTemplate_polynomial _ _
  · intro n cs hb hr
    exact cleanupCounters_uniform_bound _ cs _ hb
  · exact injectProgramTemplate_polynomial _ _ _ bound (extractionSizeStepTemplate_polynomial tm bound)

theorem extractionTermSizeProgramTemplate_exact (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (cs : ExtractionTermRegister → Nat) (hell : cs 2 ≤ cs 0) :
    (extractionTermSizeProgramTemplate tm).counters cs 12=
      (Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
        (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))).size+4 := by
  rw [extractionTermSizeProgramTemplate_value]
  exact extractionSizeContribution_exact tm e (cs 0) (cs 2) (cs 1) hell

theorem extractionTermSizeProgramTemplate_counters (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionTermSizeProgramTemplate tm).counters cs=
      Function.update (Function.update (cleanupCounters [12,5,6,7] cs) 3 (2*cs 2))
        12 (extractionSizeContribution tm (cs 2) (cs 1)) := by
  change injectedTemplateCounters extractionSizeToTermRegister _
    ((extractionSizeStepTemplate tm).counters _)=_
  rw [extractionSizeStepTemplate_counters]
  rw [injectedTemplateCounters_update _ extractionSizeToTermRegister_injective,
    injectedTemplateCounters_update _ extractionSizeToTermRegister_injective,injectedTemplateCounters_identity]
  simp [extractionSizeToTermRegister,cleanupProgramTemplate,cleanupCounters_apply]

end ShiReversibleGenerator
