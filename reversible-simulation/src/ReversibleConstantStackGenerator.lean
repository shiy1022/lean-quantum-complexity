import ReversibleConstantInitializationStart

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- Its finite alphabet depends on the machine and direction, never on n or the clock polynomial. -/
noncomputable def constantStackGeneratorCode (tm : Turing.FinTM2) (stackRank : Nat) (backward : Bool) :
    AffineLabel 0 1 (ConstantSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (Fin 3)) → CounterInstr InitializationRegister (AffineLabel 0 1 (ConstantSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (Fin 3))) :=
  affineCode (constantCellLoopCode (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward)) 0 1 (.inl 2) (.inr 0) (.inl 5) (constantSequenceExit (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) 0)

noncomputable def constantStackGeneratorSteps (tm : Turing.FinTM2) (stackRank : Nat)
    (backward : Bool) (time : Polynomial Nat) (n : Nat) (ys : List Bool) :=
  (7 * ((initializationCapacityPolynomial tm time).eval n) + 2) + descendingSteps (constantCellBody (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) ((initializationCapacityPolynomial tm time).eval n) n) (constantCellCost (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward)) ((initializationCapacityPolynomial tm time).eval n) (⟨none, initializationStartCounters tm time n, ys⟩ : CounterCfg InitializationRegister (ConstantSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (Fin 3)))

/-- Actual capacity copy followed by the complete fixed symbol/cell instruction graph. -/
theorem constantStackGenerator_run (tm : Turing.FinTM2) (stackRank : Nat) (backward : Bool)
    (time : Polynomial Nat) (n : Nat) (ys : List Bool) :
    CounterRun (constantStackGeneratorCode tm stackRank backward)
      ⟨some (affineStart 0 1 (constantSequenceExit (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) 0)), initializationPreludeCounters tm time n, ys⟩
      (constantStackGeneratorSteps tm stackRank backward time n ys)
      ⟨some (.inr (.inr (constantSequenceExit (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) 2))),
        Function.update (descendingResult (constantCellBody (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) ((initializationCapacityPolynomial tm time).eval n) n) ((initializationCapacityPolynomial tm time).eval n) (⟨none, initializationStartCounters tm time n, ys⟩ : CounterCfg InitializationRegister (ConstantSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (Fin 3)))).counters (.inr 0) 0,
        (descendingResult (constantCellBody (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) ((initializationCapacityPolynomial tm time).eval n) n) ((initializationCapacityPolynomial tm time).eval n) (⟨none, initializationStartCounters tm time n, ys⟩ : CounterCfg InitializationRegister (ConstantSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (Fin 3)))).output⟩ := by
  let cap := (initializationCapacityPolynomial tm time).eval n
  let start := (⟨none, initializationStartCounters tm time n, ys⟩ : CounterCfg InitializationRegister (ConstantSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (Fin 3)))
  let loopCode := constantCellLoopCode (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward)
  let code := constantStackGeneratorCode tm stackRank backward
  have hi := constantInitializationStart_invariant tm stackRank backward time n none ys
  have hr := constantCellTraversal_run (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) cap n cap start hi.1
  have hcopy := initializationStart_copy_run tm time n loopCode (constantSequenceExit (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) 0) ys
  have hf : ∀ l, code (Sum.inr (Sum.inr l)) = (loopCode l).relabel (fun l => Sum.inr (Sum.inr l)) := by
    intro l
    exact GeneratorOperation.code_embed (.affine (⟨.inl 2, .inr 0, 0, 1⟩ : AffineAtom InitializationRegister))
      loopCode (.inl 6) (.inl 5) (constantSequenceExit (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) 0) l
  have hr' := CounterRun.relabel loopCode code (fun l => Sum.inr (Sum.inr l)) hf hr
  dsimp only [CounterCfg.relabel, Option.map, withCounter] at hr'
  have hs : Function.update (initializationStartCounters tm time n) (.inr 0) cap = initializationStartCounters tm time n := by
    funext r
    by_cases h : r = (Sum.inr 0 : InitializationRegister) <;> simp [initializationStartCounters, cap, h]
  dsimp only [start] at hr'
  rw [hs] at hr'
  simpa [constantStackGeneratorSteps, code, start, cap] using CounterRun.trans code hcopy hr'

/-- The clock bounds actual execution of the fixed instruction program. -/
theorem constantStackGenerator_clock (tm : Turing.FinTM2) (stackRank : Nat) (backward : Bool)
    (time : Polynomial Nat) : ∃ clock : Polynomial Nat, ∀ n ys,
    constantStackGeneratorSteps tm stackRank backward time n ys ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := initializationConstantStack_polynomial_bound tm stackRank backward
    (initializationCapacityPolynomial tm time) (resourceCounterBudgetPolynomial tm time) 0
  refine ⟨Polynomial.C 7 * initializationCapacityPolynomial tm time + Polynomial.C 2 + clock, ?_⟩
  intro n ys
  have h := hc n ((initializationCapacityPolynomial tm time).eval n) (⟨none, initializationStartCounters tm time n, ys⟩ : CounterCfg InitializationRegister (ConstantSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) stackRank (Fintype.card (Option (MachineSymbol tm))) backward (initializationConstantSchedule tm backward) (Fin 3))) (by simpa only [Polynomial.eval_zero] using constantInitializationStart_invariant tm stackRank backward time n none ys)
  simpa only [constantStackGeneratorSteps, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
    Nat.add_le_add_left h (7 * ((initializationCapacityPolynomial tm time).eval n) + 2)

end ShiReversibleGenerator
