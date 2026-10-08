import ReversibleInputComponentStart
import ReversibleInputLoopExits

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

noncomputable def ascendingInputComponentCode :=
  affineCode (symbolAscendingCode header stackRank symbolCard tm e backward ars) 0 1 (.inl 2) (.inr 11) (.inl 5)
    (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 4))

noncomputable def ascendingInputComponentStartCfg (cs : InitializationRegister → Nat) (ys : List Bool) :
    CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)) := ⟨none, ascendingConstantComponentStart cs, ys⟩

noncomputable def ascendingInputComponentSteps (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :=
  (7 * cs (.inl 2) + 2) + descendingSteps (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars (cs (.inl 2)) n)
    (ascendingSymbolCellCost header stackRank symbolCard tm e backward ars) (cs (.inl 2)) (ascendingInputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys)

noncomputable def ascendingInputComponentResult (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :=
  withCounter (descendingResult (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars (cs (.inl 2)) n)
    (cs (.inl 2)) (ascendingInputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys)) (.inr 11) 0
    (symbolSequenceExit header stackRank symbolCard tm e backward ars (3 : Fin 4))

/-- The fixed component runs from any intermediate state with preserved metadata and fresh loop counters. -/
theorem ascendingInputComponent_run (n : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hz : cs (.inr 11) = 0) (hi : cs (.inr 0) = 0)
    (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (ascendingInputComponentCode header stackRank symbolCard tm e backward ars)
      ⟨some (affineStart 0 1 (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 4))), cs, ys⟩
      (ascendingInputComponentSteps header stackRank symbolCard tm e backward ars n cs ys)
      ((ascendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).relabel (fun l => Sum.inr (Sum.inr l))) := by
  let cap := cs (.inl 2)
  let state := ascendingInputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys
  let loopCode := symbolAscendingCode header stackRank symbolCard tm e backward ars
  let code := ascendingInputComponentCode header stackRank symbolCard tm e backward ars
  have hinv := ascendingInputComponentStart_invariant header stackRank symbolCard tm e backward ars cs n hn hi hb ht none ys
  have hr := ascendingSymbolCellTraversal_run header stackRank symbolCard tm e backward ars cap n cap state hinv
  have hcopy := initializationCapacity_copy_run (.inr 11) loopCode
    (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 4)) cs hz ht (by simp [AffineAtom.Valid]) ys
  have hf : ∀ l, code (Sum.inr (Sum.inr l)) = (loopCode l).relabel (fun l => Sum.inr (Sum.inr l)) := by
    intro l
    exact GeneratorOperation.code_embed (.affine (⟨.inl 2, .inr 11, 0, 1⟩ : AffineAtom InitializationRegister))
      loopCode (.inl 6) (.inl 5) (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 4)) l
  have hr' := CounterRun.relabel loopCode code (fun l => Sum.inr (Sum.inr l)) hf hr
  dsimp only [CounterCfg.relabel, Option.map, withCounter] at hr'
  have hs : Function.update (ascendingConstantComponentStart cs) (.inr 11) cap = ascendingConstantComponentStart cs := by
    funext r
    by_cases h : r = (Sum.inr 11 : InitializationRegister) <;> simp [ascendingConstantComponentStart, cap, h]
  dsimp only [state, ascendingInputComponentStartCfg] at hr'
  rw [hs] at hr'
  simpa only [ascendingInputComponentSteps, ascendingInputComponentResult, ascendingInputComponentStartCfg, ascendingConstantComponentStart,
    CounterCfg.relabel, Option.map, withCounter, code, cap] using CounterRun.trans code hcopy hr'

/-- The component exposes its designated exit for finite-program sequencing. -/
theorem ascendingInputComponent_exit :
    ascendingInputComponentCode header stackRank symbolCard tm e backward ars
      (.inr (.inr (symbolSequenceExit header stackRank symbolCard tm e backward ars (3 : Fin 4)))) = .halt := by
  have h := GeneratorOperation.code_embed (.affine (⟨.inl 2, .inr 11, 0, 1⟩ : AffineAtom InitializationRegister))
    (symbolAscendingCode header stackRank symbolCard tm e backward ars) (.inl 6) (.inl 5)
    (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 4))
    (symbolSequenceExit header stackRank symbolCard tm e backward ars (3 : Fin 4))
  rw [symbolAscending_exit] at h
  exact h

end ShiReversibleGenerator
