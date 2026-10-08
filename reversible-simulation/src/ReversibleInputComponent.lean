import ReversibleInputComponentStart
import ReversibleInputLoopExits

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

noncomputable def inputComponentCode :=
  affineCode (symbolCellLoopCode header stackRank symbolCard tm e backward ars) 0 1 (.inl 2) (.inr 0) (.inl 5)
    (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 3))

noncomputable def inputComponentStartCfg (cs : InitializationRegister → Nat) (ys : List Bool) :
    CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)) := ⟨none, constantComponentStart cs, ys⟩

noncomputable def inputComponentSteps (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :=
  (7 * cs (.inl 2) + 2) + descendingSteps (symbolCellBody header stackRank symbolCard tm e backward ars (cs (.inl 2)) n)
    (symbolCellCost header stackRank symbolCard tm e backward ars) (cs (.inl 2)) (inputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys)

noncomputable def inputComponentResult (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :=
  withCounter (descendingResult (symbolCellBody header stackRank symbolCard tm e backward ars (cs (.inl 2)) n)
    (cs (.inl 2)) (inputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys)) (.inr 0) 0
    (symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 3))

/-- The fixed component runs from any intermediate state with preserved metadata and fresh loop counters. -/
theorem inputComponent_run (n : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hz : cs (.inr 0) = 0)
    (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (inputComponentCode header stackRank symbolCard tm e backward ars)
      ⟨some (affineStart 0 1 (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 3))), cs, ys⟩
      (inputComponentSteps header stackRank symbolCard tm e backward ars n cs ys)
      ((inputComponentResult header stackRank symbolCard tm e backward ars n cs ys).relabel (fun l => Sum.inr (Sum.inr l))) := by
  let cap := cs (.inl 2)
  let state := inputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys
  let loopCode := symbolCellLoopCode header stackRank symbolCard tm e backward ars
  let code := inputComponentCode header stackRank symbolCard tm e backward ars
  have hinv := inputComponentStart_invariant header stackRank symbolCard tm e backward ars cs n hn hb ht none ys
  have hr := symbolCellTraversal_run header stackRank symbolCard tm e backward ars cap n cap state hinv
  have hcopy := initializationCapacity_copy_run (.inr 0) loopCode
    (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 3)) cs hz ht (by simp [AffineAtom.Valid]) ys
  have hf : ∀ l, code (Sum.inr (Sum.inr l)) = (loopCode l).relabel (fun l => Sum.inr (Sum.inr l)) := by
    intro l
    exact GeneratorOperation.code_embed (.affine (⟨.inl 2, .inr 0, 0, 1⟩ : AffineAtom InitializationRegister))
      loopCode (.inl 6) (.inl 5) (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 3)) l
  have hr' := CounterRun.relabel loopCode code (fun l => Sum.inr (Sum.inr l)) hf hr
  dsimp only [CounterCfg.relabel, Option.map, withCounter] at hr'
  have hs : Function.update (constantComponentStart cs) (.inr 0) cap = constantComponentStart cs := by
    funext r
    by_cases h : r = (Sum.inr 0 : InitializationRegister) <;> simp [constantComponentStart, cap, h]
  dsimp only [state, inputComponentStartCfg] at hr'
  rw [hs] at hr'
  simpa only [inputComponentSteps, inputComponentResult, inputComponentStartCfg, constantComponentStart,
    CounterCfg.relabel, Option.map, withCounter, code, cap] using CounterRun.trans code hcopy hr'

/-- The component exposes its designated exit for finite-program sequencing. -/
theorem inputComponent_exit :
    inputComponentCode header stackRank symbolCard tm e backward ars
      (.inr (.inr (symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 3)))) = .halt := by
  have h := GeneratorOperation.code_embed (.affine (⟨.inl 2, .inr 0, 0, 1⟩ : AffineAtom InitializationRegister))
    (symbolCellLoopCode header stackRank symbolCard tm e backward ars) (.inl 6) (.inl 5)
    (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 3))
    (symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 3))
  rw [symbolCellLoop_exit] at h
  exact h

end ShiReversibleGenerator
