import ReversibleExtractionSizeLoop
import ReversibleCounterBudgetCleanupClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- The accumulator's growing value does not affect the actual size-step clock. -/
theorem extractionSizeStepTemplate_cost_bound (tm : Turing.FinTM2) (cs : ExtractionSizeRegister → Nat)
    (bound : Nat) (hb : CounterBudget cs 4 bound)
    (hr : (extractionSizeStepTemplate tm).ready cs) :
    (extractionSizeStepTemplate tm).steps cs ≤
      100*bound+100+Fintype.card (Option (MachineSymbol tm))*7 := by
  have h1 := hb 1 (by decide)
  have h2 := hb 2 (by decide)
  have h3 := hb 3 (by decide)
  obtain ⟨h5,h6,h7⟩ := (extractionSizeStepTemplate_ready tm cs).1 hr
  have hc0 := comparisonSteps_bound (cs 2) 0
  have hc1 := comparisonSteps_bound (cs 2+1) (cs 1)
  have hc2 := comparisonSteps_bound (cs 1) (2*cs 2)
  simp [extractionSizeStepTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    extractionSizeBaseTemplate,extractionSizePayloadTemplate,guardedProgramTemplate,
    extractionSizeGuardRegisters,extractionSizeAdd,counterAffineAccumulationProgramTemplate,
    identityProgramTemplate,AffineAtom.apply,AffineAtom.steps,indexGuardSteps,indexExpressionSteps,
    TickIndexExpr.seed,TickIndexExpr.updates,TickIndexSeed.coefficient,TickIndexSeed.source,
    TickIndexSeed.offset,indexUpdateSteps,IndexUpdate.amount,TickIndexExpr.eval,TickIndexGuard.eval,
    h5,h6] at ⊢
  split_ifs <;> simp_all <;> omega

/-- A step preserves the uniform non-accumulator budget when the length counter is half that budget. -/
theorem extractionSizeStepTemplate_counter_budget (tm : Turing.FinTM2) (cs : ExtractionSizeRegister → Nat)
    (bound : Nat) (hb : CounterBudget cs 4 (2*bound)) (hell : cs 2 ≤ bound) :
    CounterBudget ((extractionSizeStepTemplate tm).counters cs) 4 (2*bound) := by
  intro q hq
  rw [extractionSizeStepTemplate_counters]
  by_cases h3 : q=3
  · subst q; simp; omega
  · simpa [Function.update_of_ne hq,Function.update_of_ne h3] using hb q hq

end ShiReversibleGenerator
