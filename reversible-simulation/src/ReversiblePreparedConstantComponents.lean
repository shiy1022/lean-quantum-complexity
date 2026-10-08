import ReversibleInitializationLoopReset

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

noncomputable def preparedConstantComponentCode :=
  cleanupCode initializationLoopReset (constantComponentCode header stackRank symbolCard backward ars) (affineStart 0 1 (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 3)))

noncomputable def preparedConstantComponentSteps (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :=
  cleanupSteps initializationLoopReset cs +
    constantComponentSteps header stackRank symbolCard backward ars n (cleanupCounters initializationLoopReset cs) ys

noncomputable def preparedConstantComponentResult (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    CounterCfg InitializationRegister (CleanupLabels initializationLoopReset (AffineLabel 0 1 (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)))) :=
  ((constantComponentResult header stackRank symbolCard backward ars n (cleanupCounters initializationLoopReset cs) ys).relabel
    (fun l => Sum.inr (Sum.inr l))).relabel (cleanupExit initializationLoopReset)

/-- Actual loop-counter cleanup makes the component composable after any preceding initializer component. -/
theorem preparedConstantComponent_run (n : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (preparedConstantComponentCode header stackRank symbolCard backward ars)
      ⟨some (cleanupEntry initializationLoopReset (affineStart 0 1 (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 3)))), cs, ys⟩
      (preparedConstantComponentSteps header stackRank symbolCard backward ars n cs ys) (preparedConstantComponentResult header stackRank symbolCard backward ars n cs ys) := by
  let reset := cleanupCounters initializationLoopReset cs
  let code := preparedConstantComponentCode header stackRank symbolCard backward ars
  have hc := cleanupCode_run initializationLoopReset (constantComponentCode header stackRank symbolCard backward ars) (affineStart 0 1 (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 3))) cs ys
  have hr := constantComponent_run header stackRank symbolCard backward ars n reset
    (by simpa [reset, initializationLoopReset_metadata] using hn)
    (initializationLoopReset_index cs)
    
    (by simpa [reset, initializationLoopReset_metadata] using hb)
    (by simpa [reset, initializationLoopReset_metadata] using ht) ys
  have hr' := CounterRun.relabel (constantComponentCode header stackRank symbolCard backward ars) code (cleanupExit initializationLoopReset)
    (cleanupCode_embed initializationLoopReset (constantComponentCode header stackRank symbolCard backward ars) (affineStart 0 1 (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 3)))) hr
  simpa only [preparedConstantComponentSteps, preparedConstantComponentResult, CounterCfg.relabel, Option.map,
    reset, code] using CounterRun.trans code hc hr'

/-- The reset cost and actual component clock both fit one polynomial at every intermediate state. -/
theorem preparedConstantComponent_polynomial_bound (capacity budget layers : Polynomial Nat)
    (haddr : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat) (ys : List Bool),
      cs (.inl 0) = n → cs (.inl 2) = capacity.eval n → cs (.inl 6) = 0 → cs (.inl 5) = 0 →
      CounterBudget cs (.inr 10) (budget.eval n) → cs (.inr 10) ≤ layers.eval n →
      preparedConstantComponentSteps header stackRank symbolCard backward ars n cs ys ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := constantComponent_polynomial_bound header stackRank symbolCard backward ars capacity budget layers haddr
  refine ⟨Polynomial.C 4 * budget + Polynomial.C 2 + clock, ?_⟩
  intro n cs ys hn hcap hb ht hbudget hl
  have h := hc n (cleanupCounters initializationLoopReset cs) ys
    (by simpa [initializationLoopReset_metadata] using hn)
    (by simpa [initializationLoopReset_metadata] using hcap)
    
    (by simpa [initializationLoopReset_metadata] using hb)
    (by simpa [initializationLoopReset_metadata] using ht)
    (initializationLoopReset_budget cs (budget.eval n) hbudget)
    (by simpa [initializationLoopReset_layers] using hl)
  simpa only [preparedConstantComponentSteps, Polynomial.eval_add] using
    Nat.add_le_add (initializationLoopReset_clock budget n cs hbudget) h

noncomputable def preparedAscendingConstantComponentCode :=
  cleanupCode initializationLoopReset (ascendingConstantComponentCode header stackRank symbolCard backward ars) (affineStart 0 1 (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 4)))

noncomputable def preparedAscendingConstantComponentSteps (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :=
  cleanupSteps initializationLoopReset cs +
    ascendingConstantComponentSteps header stackRank symbolCard backward ars n (cleanupCounters initializationLoopReset cs) ys

noncomputable def preparedAscendingConstantComponentResult (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    CounterCfg InitializationRegister (CleanupLabels initializationLoopReset (AffineLabel 0 1 (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)))) :=
  ((ascendingConstantComponentResult header stackRank symbolCard backward ars n (cleanupCounters initializationLoopReset cs) ys).relabel
    (fun l => Sum.inr (Sum.inr l))).relabel (cleanupExit initializationLoopReset)

/-- Actual loop-counter cleanup makes the component composable after any preceding initializer component. -/
theorem preparedAscendingConstantComponent_run (n : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (preparedAscendingConstantComponentCode header stackRank symbolCard backward ars)
      ⟨some (cleanupEntry initializationLoopReset (affineStart 0 1 (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 4)))), cs, ys⟩
      (preparedAscendingConstantComponentSteps header stackRank symbolCard backward ars n cs ys) (preparedAscendingConstantComponentResult header stackRank symbolCard backward ars n cs ys) := by
  let reset := cleanupCounters initializationLoopReset cs
  let code := preparedAscendingConstantComponentCode header stackRank symbolCard backward ars
  have hc := cleanupCode_run initializationLoopReset (ascendingConstantComponentCode header stackRank symbolCard backward ars) (affineStart 0 1 (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 4))) cs ys
  have hr := ascendingConstantComponent_run header stackRank symbolCard backward ars n reset
    (by simpa [reset, initializationLoopReset_metadata] using hn)
    (initializationLoopReset_remaining cs)
    (initializationLoopReset_index cs)
    (by simpa [reset, initializationLoopReset_metadata] using hb)
    (by simpa [reset, initializationLoopReset_metadata] using ht) ys
  have hr' := CounterRun.relabel (ascendingConstantComponentCode header stackRank symbolCard backward ars) code (cleanupExit initializationLoopReset)
    (cleanupCode_embed initializationLoopReset (ascendingConstantComponentCode header stackRank symbolCard backward ars) (affineStart 0 1 (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 4)))) hr
  simpa only [preparedAscendingConstantComponentSteps, preparedAscendingConstantComponentResult, CounterCfg.relabel, Option.map,
    reset, code] using CounterRun.trans code hc hr'

/-- The reset cost and actual component clock both fit one polynomial at every intermediate state. -/
theorem preparedAscendingConstantComponent_polynomial_bound (capacity budget layers : Polynomial Nat)
    (haddr : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    ∃ clock : Polynomial Nat, ∀ n (cs : InitializationRegister → Nat) (ys : List Bool),
      cs (.inl 0) = n → cs (.inl 2) = capacity.eval n → cs (.inl 6) = 0 → cs (.inl 5) = 0 →
      CounterBudget cs (.inr 10) (budget.eval n) → cs (.inr 10) ≤ layers.eval n →
      preparedAscendingConstantComponentSteps header stackRank symbolCard backward ars n cs ys ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := ascendingConstantComponent_polynomial_bound header stackRank symbolCard backward ars capacity budget layers haddr
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
  simpa only [preparedAscendingConstantComponentSteps, Polynomial.eval_add] using
    Nat.add_le_add (initializationLoopReset_clock budget n cs hbudget) h

end ShiReversibleGenerator
