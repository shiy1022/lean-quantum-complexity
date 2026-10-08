import ReversibleInitializationStart

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- Its finite alphabet depends on the machine and direction, never on n or the clock polynomial. -/
noncomputable def inputStackGeneratorCode (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) :
    AffineLabel 0 1 (SymbolSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (Fin 3)) → CounterInstr InitializationRegister (AffineLabel 0 1 (SymbolSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (Fin 3))) :=
  affineCode (symbolCellLoopCode (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward)) 0 1 (.inl 2) (.inr 0) (.inl 5) (symbolSequenceExit (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) 0)

noncomputable def inputStackGeneratorSteps (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (time : Polynomial Nat) (n : Nat) (ys : List Bool) :=
  (7 * ((initializationCapacityPolynomial tm time).eval n) + 2) + descendingSteps (symbolCellBody (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) ((initializationCapacityPolynomial tm time).eval n) n) (symbolCellCost (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward)) ((initializationCapacityPolynomial tm time).eval n) (⟨none, initializationStartCounters tm time n, ys⟩ : CounterCfg InitializationRegister (SymbolSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (Fin 3)))

/-- Actual capacity copy followed by the complete fixed symbol/cell instruction graph. -/
theorem inputStackGenerator_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool)
    (time : Polynomial Nat) (n : Nat) (ys : List Bool) :
    CounterRun (inputStackGeneratorCode tm e backward)
      ⟨some (affineStart 0 1 (symbolSequenceExit (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) 0)), initializationPreludeCounters tm time n, ys⟩
      (inputStackGeneratorSteps tm e backward time n ys)
      ⟨some (.inr (.inr (symbolSequenceExit (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) 2))),
        Function.update (descendingResult (symbolCellBody (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) ((initializationCapacityPolynomial tm time).eval n) n) ((initializationCapacityPolynomial tm time).eval n) (⟨none, initializationStartCounters tm time n, ys⟩ : CounterCfg InitializationRegister (SymbolSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (Fin 3)))).counters (.inr 0) 0,
        (descendingResult (symbolCellBody (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) ((initializationCapacityPolynomial tm time).eval n) n) ((initializationCapacityPolynomial tm time).eval n) (⟨none, initializationStartCounters tm time n, ys⟩ : CounterCfg InitializationRegister (SymbolSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (Fin 3)))).output⟩ := by
  let cap := (initializationCapacityPolynomial tm time).eval n
  let start := (⟨none, initializationStartCounters tm time n, ys⟩ : CounterCfg InitializationRegister (SymbolSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (Fin 3)))
  let loopCode := symbolCellLoopCode (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward)
  let code := inputStackGeneratorCode tm e backward
  have hi := initializationStart_invariant tm e backward time n none ys
  have hr := symbolCellTraversal_run (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) cap n cap start hi.1
  have hcopy := initializationStart_copy_run tm time n loopCode (symbolSequenceExit (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) 0) ys
  have hf : ∀ l, code (Sum.inr (Sum.inr l)) = (loopCode l).relabel (fun l => Sum.inr (Sum.inr l)) := by
    intro l
    exact GeneratorOperation.code_embed (.affine (⟨.inl 2, .inr 0, 0, 1⟩ : AffineAtom InitializationRegister))
      loopCode (.inl 6) (.inl 5) (symbolSequenceExit (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) 0) l
  have hr' := CounterRun.relabel loopCode code (fun l => Sum.inr (Sum.inr l)) hf hr
  dsimp only [CounterCfg.relabel, Option.map, withCounter] at hr'
  have hs : Function.update (initializationStartCounters tm time n) (.inr 0) cap = initializationStartCounters tm time n := by
    funext r
    by_cases h : r = (Sum.inr 0 : InitializationRegister) <;> simp [initializationStartCounters, cap, h]
  dsimp only [start] at hr'
  rw [hs] at hr'
  simpa [inputStackGeneratorSteps, code, start, cap] using CounterRun.trans code hcopy hr'

/-- The clock bounds actual execution of the fixed instruction program. -/
theorem inputStackGenerator_clock (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool)
    (time : Polynomial Nat) : ∃ clock : Polynomial Nat, ∀ n ys,
    inputStackGeneratorSteps tm e backward time n ys ≤ clock.eval n := by
  obtain ⟨clock, hc⟩ := initializationInputStack_polynomial_bound tm e backward
    (initializationCapacityPolynomial tm time) (resourceCounterBudgetPolynomial tm time) 0
  refine ⟨Polynomial.C 7 * initializationCapacityPolynomial tm time + Polynomial.C 2 + clock, ?_⟩
  intro n ys
  have h := hc n ((initializationCapacityPolynomial tm time).eval n) (⟨none, initializationStartCounters tm time n, ys⟩ : CounterCfg InitializationRegister (SymbolSequenceLabels (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (Fin 3))) (by simpa only [Polynomial.eval_zero] using initializationStart_invariant tm e backward time n none ys)
  simpa only [inputStackGeneratorSteps, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] using
    Nat.add_le_add_left h (7 * ((initializationCapacityPolynomial tm time).eval n) + 2)

end ShiReversibleGenerator
