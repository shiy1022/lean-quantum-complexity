import ReversibleConstantComponentStart
import ReversibleConstantLoopExits

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

noncomputable def ascendingConstantComponentCode :=
  affineCode (constantAscendingCode header stackRank symbolCard backward ars) 0 1 (.inl 2) (.inr 11) (.inl 5)
    (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 4))

noncomputable def ascendingConstantComponentStartCfg (cs : InitializationRegister → Nat) (ys : List Bool) :
    CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)) := ⟨none, ascendingConstantComponentStart cs, ys⟩

noncomputable def ascendingConstantComponentSteps (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :=
  (7 * cs (.inl 2) + 2) + descendingSteps (ascendingConstantCellBody header stackRank symbolCard backward ars (cs (.inl 2)) n)
    (ascendingConstantCellCost header stackRank symbolCard backward ars) (cs (.inl 2)) (ascendingConstantComponentStartCfg header stackRank symbolCard backward ars cs ys)

noncomputable def ascendingConstantComponentResult (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :=
  withCounter (descendingResult (ascendingConstantCellBody header stackRank symbolCard backward ars (cs (.inl 2)) n)
    (cs (.inl 2)) (ascendingConstantComponentStartCfg header stackRank symbolCard backward ars cs ys)) (.inr 11) 0
    (constantSequenceExit header stackRank symbolCard backward ars (3 : Fin 4))

/-- The fixed component runs from any intermediate state with preserved metadata and fresh loop counters. -/
theorem ascendingConstantComponent_run (n : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hz : cs (.inr 11) = 0) (hi : cs (.inr 0) = 0)
    (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (ascendingConstantComponentCode header stackRank symbolCard backward ars)
      ⟨some (affineStart 0 1 (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 4))), cs, ys⟩
      (ascendingConstantComponentSteps header stackRank symbolCard backward ars n cs ys)
      ((ascendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).relabel (fun l => Sum.inr (Sum.inr l))) := by
  let cap := cs (.inl 2)
  let state := ascendingConstantComponentStartCfg header stackRank symbolCard backward ars cs ys
  let loopCode := constantAscendingCode header stackRank symbolCard backward ars
  let code := ascendingConstantComponentCode header stackRank symbolCard backward ars
  have hinv := ascendingConstantComponentStart_invariant header stackRank symbolCard backward ars cs n hn hi hb ht none ys
  have hr := ascendingConstantCellTraversal_run header stackRank symbolCard backward ars cap n cap state hinv
  have hcopy := initializationCapacity_copy_run (.inr 11) loopCode
    (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 4)) cs hz ht (by simp [AffineAtom.Valid]) ys
  have hf : ∀ l, code (Sum.inr (Sum.inr l)) = (loopCode l).relabel (fun l => Sum.inr (Sum.inr l)) := by
    intro l
    exact GeneratorOperation.code_embed (.affine (⟨.inl 2, .inr 11, 0, 1⟩ : AffineAtom InitializationRegister))
      loopCode (.inl 6) (.inl 5) (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 4)) l
  have hr' := CounterRun.relabel loopCode code (fun l => Sum.inr (Sum.inr l)) hf hr
  dsimp only [CounterCfg.relabel, Option.map, withCounter] at hr'
  have hs : Function.update (ascendingConstantComponentStart cs) (.inr 11) cap = ascendingConstantComponentStart cs := by
    funext r
    by_cases h : r = (Sum.inr 11 : InitializationRegister) <;> simp [ascendingConstantComponentStart, cap, h]
  dsimp only [state, ascendingConstantComponentStartCfg] at hr'
  rw [hs] at hr'
  simpa only [ascendingConstantComponentSteps, ascendingConstantComponentResult, ascendingConstantComponentStartCfg, ascendingConstantComponentStart,
    CounterCfg.relabel, Option.map, withCounter, code, cap] using CounterRun.trans code hcopy hr'

/-- The component exposes its designated exit for finite-program sequencing. -/
theorem ascendingConstantComponent_exit :
    ascendingConstantComponentCode header stackRank symbolCard backward ars
      (.inr (.inr (constantSequenceExit header stackRank symbolCard backward ars (3 : Fin 4)))) = .halt := by
  have h := GeneratorOperation.code_embed (.affine (⟨.inl 2, .inr 11, 0, 1⟩ : AffineAtom InitializationRegister))
    (constantAscendingCode header stackRank symbolCard backward ars) (.inl 6) (.inl 5)
    (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 4))
    (constantSequenceExit header stackRank symbolCard backward ars (3 : Fin 4))
  rw [constantAscending_exit] at h
  exact h

end ShiReversibleGenerator
