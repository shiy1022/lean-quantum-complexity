import ReversibleInitializationLoopReset
import ReversibleInputComponentClock

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

noncomputable def preparedInputComponentCode :=
  cleanupCode initializationLoopReset (inputComponentCode header stackRank symbolCard tm e backward ars) (affineStart 0 1 (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 3)))

noncomputable def preparedInputComponentSteps (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :=
  cleanupSteps initializationLoopReset cs +
    inputComponentSteps header stackRank symbolCard tm e backward ars n (cleanupCounters initializationLoopReset cs) ys

noncomputable def preparedInputComponentResult (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    CounterCfg InitializationRegister (CleanupLabels initializationLoopReset (AffineLabel 0 1 (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))) :=
  ((inputComponentResult header stackRank symbolCard tm e backward ars n (cleanupCounters initializationLoopReset cs) ys).relabel
    (fun l => Sum.inr (Sum.inr l))).relabel (cleanupExit initializationLoopReset)

/-- Actual loop-counter cleanup makes the component composable after any preceding initializer component. -/
theorem preparedInputComponent_run (n : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (preparedInputComponentCode header stackRank symbolCard tm e backward ars)
      ⟨some (cleanupEntry initializationLoopReset (affineStart 0 1 (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 3)))), cs, ys⟩
      (preparedInputComponentSteps header stackRank symbolCard tm e backward ars n cs ys) (preparedInputComponentResult header stackRank symbolCard tm e backward ars n cs ys) := by
  let reset := cleanupCounters initializationLoopReset cs
  let code := preparedInputComponentCode header stackRank symbolCard tm e backward ars
  have hc := cleanupCode_run initializationLoopReset (inputComponentCode header stackRank symbolCard tm e backward ars) (affineStart 0 1 (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 3))) cs ys
  have hr := inputComponent_run header stackRank symbolCard tm e backward ars n reset
    (by simpa [reset, initializationLoopReset_metadata] using hn)
    (initializationLoopReset_index cs)
    
    (by simpa [reset, initializationLoopReset_metadata] using hb)
    (by simpa [reset, initializationLoopReset_metadata] using ht) ys
  have hr' := CounterRun.relabel (inputComponentCode header stackRank symbolCard tm e backward ars) code (cleanupExit initializationLoopReset)
    (cleanupCode_embed initializationLoopReset (inputComponentCode header stackRank symbolCard tm e backward ars) (affineStart 0 1 (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 3)))) hr
  simpa only [preparedInputComponentSteps, preparedInputComponentResult, CounterCfg.relabel, Option.map,
    reset, code] using CounterRun.trans code hc hr'

/-- The reset cost and actual component clock both fit one polynomial at every intermediate state. -/
theorem preparedInputComponent_polynomial_bound (capacity budget layers : Polynomial Nat)
    (haddr : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat) (ys : List Bool),
      cs (.inl 0) = n → cs (.inl 2) = capacity.eval n → cs (.inl 6) = 0 → cs (.inl 5) = 0 →
      CounterBudget cs (.inr 10) (budget.eval n) → cs (.inr 10) ≤ layers.eval n →
      preparedInputComponentSteps header stackRank symbolCard tm e backward ars n cs ys ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := inputComponent_polynomial_bound header stackRank symbolCard tm e backward ars capacity budget layers haddr
  refine ⟨Polynomial.C 4 * budget + Polynomial.C 2 + clock, ?_⟩
  intro n cs ys hn hcap hb ht hbudget hl
  have h := hc n (cleanupCounters initializationLoopReset cs) ys
    (by simpa [initializationLoopReset_metadata] using hn)
    (by simpa [initializationLoopReset_metadata] using hcap)
    
    (by simpa [initializationLoopReset_metadata] using hb)
    (by simpa [initializationLoopReset_metadata] using ht)
    (initializationLoopReset_budget cs (budget.eval n) hbudget)
    (by simpa [initializationLoopReset_layers] using hl)
  simpa only [preparedInputComponentSteps, Polynomial.eval_add] using
    Nat.add_le_add (initializationLoopReset_clock budget n cs hbudget) h

noncomputable def preparedAscendingInputComponentCode :=
  cleanupCode initializationLoopReset (ascendingInputComponentCode header stackRank symbolCard tm e backward ars) (affineStart 0 1 (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 4)))

noncomputable def preparedAscendingInputComponentSteps (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :=
  cleanupSteps initializationLoopReset cs +
    ascendingInputComponentSteps header stackRank symbolCard tm e backward ars n (cleanupCounters initializationLoopReset cs) ys

noncomputable def preparedAscendingInputComponentResult (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    CounterCfg InitializationRegister (CleanupLabels initializationLoopReset (AffineLabel 0 1 (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))) :=
  ((ascendingInputComponentResult header stackRank symbolCard tm e backward ars n (cleanupCounters initializationLoopReset cs) ys).relabel
    (fun l => Sum.inr (Sum.inr l))).relabel (cleanupExit initializationLoopReset)

/-- Actual loop-counter cleanup makes the component composable after any preceding initializer component. -/
theorem preparedAscendingInputComponent_run (n : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (preparedAscendingInputComponentCode header stackRank symbolCard tm e backward ars)
      ⟨some (cleanupEntry initializationLoopReset (affineStart 0 1 (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 4)))), cs, ys⟩
      (preparedAscendingInputComponentSteps header stackRank symbolCard tm e backward ars n cs ys) (preparedAscendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys) := by
  let reset := cleanupCounters initializationLoopReset cs
  let code := preparedAscendingInputComponentCode header stackRank symbolCard tm e backward ars
  have hc := cleanupCode_run initializationLoopReset (ascendingInputComponentCode header stackRank symbolCard tm e backward ars) (affineStart 0 1 (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 4))) cs ys
  have hr := ascendingInputComponent_run header stackRank symbolCard tm e backward ars n reset
    (by simpa [reset, initializationLoopReset_metadata] using hn)
    (initializationLoopReset_remaining cs)
    (initializationLoopReset_index cs)
    (by simpa [reset, initializationLoopReset_metadata] using hb)
    (by simpa [reset, initializationLoopReset_metadata] using ht) ys
  have hr' := CounterRun.relabel (ascendingInputComponentCode header stackRank symbolCard tm e backward ars) code (cleanupExit initializationLoopReset)
    (cleanupCode_embed initializationLoopReset (ascendingInputComponentCode header stackRank symbolCard tm e backward ars) (affineStart 0 1 (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 4)))) hr
  simpa only [preparedAscendingInputComponentSteps, preparedAscendingInputComponentResult, CounterCfg.relabel, Option.map,
    reset, code] using CounterRun.trans code hc hr'

/-- The reset cost and actual component clock both fit one polynomial at every intermediate state. -/
theorem preparedAscendingInputComponent_polynomial_bound (capacity budget layers : Polynomial Nat)
    (haddr : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat) (ys : List Bool),
      cs (.inl 0) = n → cs (.inl 2) = capacity.eval n → cs (.inl 6) = 0 → cs (.inl 5) = 0 →
      CounterBudget cs (.inr 10) (budget.eval n) → cs (.inr 10) ≤ layers.eval n →
      preparedAscendingInputComponentSteps header stackRank symbolCard tm e backward ars n cs ys ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := ascendingInputComponent_polynomial_bound header stackRank symbolCard tm e backward ars capacity budget layers haddr
  refine ⟨Polynomial.C 4 * budget + Polynomial.C 2 + clock, ?_⟩
  intro n cs ys hn hcap hb ht hbudget hl
  have h := hc n (cleanupCounters initializationLoopReset cs) ys
    (by simpa [initializationLoopReset_metadata] using hn)
    (by simpa [initializationLoopReset_metadata] using hcap)
    (initializationLoopReset_index cs)
    (by simpa [initializationLoopReset_metadata] using hb)
    (by simpa [initializationLoopReset_metadata] using ht)
    (initializationLoopReset_budget cs (budget.eval n) hbudget)
    (by simpa [initializationLoopReset_layers] using hl)
  simpa only [preparedAscendingInputComponentSteps, Polynomial.eval_add] using
    Nat.add_le_add (initializationLoopReset_clock budget n cs hbudget) h

end ShiReversibleGenerator
