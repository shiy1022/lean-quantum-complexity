import ReversibleConstantComponentStart
import ReversibleConstantLoopExits

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

noncomputable def constantComponentCode :=
  affineCode (constantCellLoopCode header stackRank symbolCard backward ars) 0 1 (.inl 2) (.inr 0) (.inl 5)
    (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 3))

noncomputable def constantComponentStartCfg (cs : InitializationRegister → Nat) (ys : List Bool) :
    CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)) := ⟨none, constantComponentStart cs, ys⟩

noncomputable def constantComponentSteps (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :=
  (7 * cs (.inl 2) + 2) + descendingSteps (constantCellBody header stackRank symbolCard backward ars (cs (.inl 2)) n)
    (constantCellCost header stackRank symbolCard backward ars) (cs (.inl 2)) (constantComponentStartCfg header stackRank symbolCard backward ars cs ys)

noncomputable def constantComponentResult (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :=
  withCounter (descendingResult (constantCellBody header stackRank symbolCard backward ars (cs (.inl 2)) n)
    (cs (.inl 2)) (constantComponentStartCfg header stackRank symbolCard backward ars cs ys)) (.inr 0) 0
    (constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 3))

/-- The fixed component runs from any intermediate state with preserved metadata and fresh loop counters. -/
theorem constantComponent_run (n : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hz : cs (.inr 0) = 0)
    (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0) (ys : List Bool) :
    CounterRun (constantComponentCode header stackRank symbolCard backward ars)
      ⟨some (affineStart 0 1 (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 3))), cs, ys⟩
      (constantComponentSteps header stackRank symbolCard backward ars n cs ys)
      ((constantComponentResult header stackRank symbolCard backward ars n cs ys).relabel (fun l => Sum.inr (Sum.inr l))) := by
  let cap := cs (.inl 2)
  let state := constantComponentStartCfg header stackRank symbolCard backward ars cs ys
  let loopCode := constantCellLoopCode header stackRank symbolCard backward ars
  let code := constantComponentCode header stackRank symbolCard backward ars
  have hinv := constantComponentStart_invariant header stackRank symbolCard backward ars cs n hn hb ht none ys
  have hr := constantCellTraversal_run header stackRank symbolCard backward ars cap n cap state hinv
  have hcopy := initializationCapacity_copy_run (.inr 0) loopCode
    (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 3)) cs hz ht (by simp [AffineAtom.Valid]) ys
  have hf : ∀ l, code (Sum.inr (Sum.inr l)) = (loopCode l).relabel (fun l => Sum.inr (Sum.inr l)) := by
    intro l
    exact GeneratorOperation.code_embed (.affine (⟨.inl 2, .inr 0, 0, 1⟩ : AffineAtom InitializationRegister))
      loopCode (.inl 6) (.inl 5) (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 3)) l
  have hr' := CounterRun.relabel loopCode code (fun l => Sum.inr (Sum.inr l)) hf hr
  dsimp only [CounterCfg.relabel, Option.map, withCounter] at hr'
  have hs : Function.update (constantComponentStart cs) (.inr 0) cap = constantComponentStart cs := by
    funext r
    by_cases h : r = (Sum.inr 0 : InitializationRegister) <;> simp [constantComponentStart, cap, h]
  dsimp only [state, constantComponentStartCfg] at hr'
  rw [hs] at hr'
  simpa only [constantComponentSteps, constantComponentResult, constantComponentStartCfg, constantComponentStart,
    CounterCfg.relabel, Option.map, withCounter, code, cap] using CounterRun.trans code hcopy hr'

/-- The component exposes its designated exit for finite-program sequencing. -/
theorem constantComponent_exit :
    constantComponentCode header stackRank symbolCard backward ars
      (.inr (.inr (constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 3)))) = .halt := by
  have h := GeneratorOperation.code_embed (.affine (⟨.inl 2, .inr 0, 0, 1⟩ : AffineAtom InitializationRegister))
    (constantCellLoopCode header stackRank symbolCard backward ars) (.inl 6) (.inl 5)
    (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 3))
    (constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 3))
  rw [constantCellLoop_exit] at h
  exact h

end ShiReversibleGenerator
