import ReversibleInitializerSequence

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM

section
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

set_option backward.isDefEq.respectTransparency false in
/-- Package the verified instruction graph; runtime and source frames are its actual proofs. -/
noncomputable def packagedConstantComponent : InitializationComponent := by
  classical
  refine {
    Labels := CleanupLabels initializationLoopReset (AffineLabel 0 1 (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)))
    finiteLabels := inferInstance
    decideLabels := inferInstance
    code := preparedConstantComponentCode header stackRank symbolCard backward ars
    entry := cleanupEntry initializationLoopReset (affineStart 0 1 (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 3)))
    exit := cleanupExit initializationLoopReset (.inr (.inr (constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 3))) : AffineLabel 0 1 (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)))
    exit_halt := preparedConstantComponent_exit header stackRank symbolCard backward ars
    steps := preparedConstantComponentSteps header stackRank symbolCard backward ars
    counters := fun n cs ys => (preparedConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters
    output := fun n cs ys => (preparedConstantComponentResult header stackRank symbolCard backward ars n cs ys).output
    metadata := preparedConstantComponentResult_metadata header stackRank symbolCard backward ars
    run := ?_ }
  intro n cs ys hn hb ht
  have h := preparedConstantComponent_run header stackRank symbolCard backward ars n cs hn hb ht ys
  have he : preparedConstantComponentResult header stackRank symbolCard backward ars n cs ys =
      ⟨some (cleanupExit initializationLoopReset (.inr (.inr (constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 3))) : AffineLabel 0 1 (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)))), (preparedConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters, (preparedConstantComponentResult header stackRank symbolCard backward ars n cs ys).output⟩ := by
    apply CounterCfg.ext
    · exact preparedConstantComponentResult_pc header stackRank symbolCard backward ars n cs ys
    · rfl
    · rfl
  rw [he] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Package the verified instruction graph; runtime and source frames are its actual proofs. -/
noncomputable def packagedAscendingConstantComponent : InitializationComponent := by
  classical
  refine {
    Labels := CleanupLabels initializationLoopReset (AffineLabel 0 1 (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)))
    finiteLabels := inferInstance
    decideLabels := inferInstance
    code := preparedAscendingConstantComponentCode header stackRank symbolCard backward ars
    entry := cleanupEntry initializationLoopReset (affineStart 0 1 (constantSequenceExit header stackRank symbolCard backward ars (0 : Fin 4)))
    exit := cleanupExit initializationLoopReset (.inr (.inr (constantSequenceExit header stackRank symbolCard backward ars (3 : Fin 4))) : AffineLabel 0 1 (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)))
    exit_halt := preparedAscendingConstantComponent_exit header stackRank symbolCard backward ars
    steps := preparedAscendingConstantComponentSteps header stackRank symbolCard backward ars
    counters := fun n cs ys => (preparedAscendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters
    output := fun n cs ys => (preparedAscendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).output
    metadata := preparedAscendingConstantComponentResult_metadata header stackRank symbolCard backward ars
    run := ?_ }
  intro n cs ys hn hb ht
  have h := preparedAscendingConstantComponent_run header stackRank symbolCard backward ars n cs hn hb ht ys
  have he : preparedAscendingConstantComponentResult header stackRank symbolCard backward ars n cs ys =
      ⟨some (cleanupExit initializationLoopReset (.inr (.inr (constantSequenceExit header stackRank symbolCard backward ars (3 : Fin 4))) : AffineLabel 0 1 (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)))), (preparedAscendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters, (preparedAscendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).output⟩ := by
    apply CounterCfg.ext
    · exact preparedAscendingConstantComponentResult_pc header stackRank symbolCard backward ars n cs ys
    · rfl
    · rfl
  rw [he] at h
  exact h

end

section
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

set_option backward.isDefEq.respectTransparency false in
/-- Package the verified instruction graph; runtime and source frames are its actual proofs. -/
noncomputable def packagedInputComponent : InitializationComponent := by
  classical
  refine {
    Labels := CleanupLabels initializationLoopReset (AffineLabel 0 1 (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))
    finiteLabels := inferInstance
    decideLabels := inferInstance
    code := preparedInputComponentCode header stackRank symbolCard tm e backward ars
    entry := cleanupEntry initializationLoopReset (affineStart 0 1 (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 3)))
    exit := cleanupExit initializationLoopReset (.inr (.inr (symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 3))) : AffineLabel 0 1 (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))
    exit_halt := preparedInputComponent_exit header stackRank symbolCard tm e backward ars
    steps := preparedInputComponentSteps header stackRank symbolCard tm e backward ars
    counters := fun n cs ys => (preparedInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters
    output := fun n cs ys => (preparedInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).output
    metadata := preparedInputComponentResult_metadata header stackRank symbolCard tm e backward ars
    run := ?_ }
  intro n cs ys hn hb ht
  have h := preparedInputComponent_run header stackRank symbolCard tm e backward ars n cs hn hb ht ys
  have he : preparedInputComponentResult header stackRank symbolCard tm e backward ars n cs ys =
      ⟨some (cleanupExit initializationLoopReset (.inr (.inr (symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 3))) : AffineLabel 0 1 (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))), (preparedInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters, (preparedInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).output⟩ := by
    apply CounterCfg.ext
    · exact preparedInputComponentResult_pc header stackRank symbolCard tm e backward ars n cs ys
    · rfl
    · rfl
  rw [he] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Package the verified instruction graph; runtime and source frames are its actual proofs. -/
noncomputable def packagedAscendingInputComponent : InitializationComponent := by
  classical
  refine {
    Labels := CleanupLabels initializationLoopReset (AffineLabel 0 1 (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))
    finiteLabels := inferInstance
    decideLabels := inferInstance
    code := preparedAscendingInputComponentCode header stackRank symbolCard tm e backward ars
    entry := cleanupEntry initializationLoopReset (affineStart 0 1 (symbolSequenceExit header stackRank symbolCard tm e backward ars (0 : Fin 4)))
    exit := cleanupExit initializationLoopReset (.inr (.inr (symbolSequenceExit header stackRank symbolCard tm e backward ars (3 : Fin 4))) : AffineLabel 0 1 (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))
    exit_halt := preparedAscendingInputComponent_exit header stackRank symbolCard tm e backward ars
    steps := preparedAscendingInputComponentSteps header stackRank symbolCard tm e backward ars
    counters := fun n cs ys => (preparedAscendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters
    output := fun n cs ys => (preparedAscendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).output
    metadata := preparedAscendingInputComponentResult_metadata header stackRank symbolCard tm e backward ars
    run := ?_ }
  intro n cs ys hn hb ht
  have h := preparedAscendingInputComponent_run header stackRank symbolCard tm e backward ars n cs hn hb ht ys
  have he : preparedAscendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys =
      ⟨some (cleanupExit initializationLoopReset (.inr (.inr (symbolSequenceExit header stackRank symbolCard tm e backward ars (3 : Fin 4))) : AffineLabel 0 1 (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))), (preparedAscendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters, (preparedAscendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).output⟩ := by
    apply CounterCfg.ext
    · exact preparedAscendingInputComponentResult_pc header stackRank symbolCard tm e backward ars n cs ys
    · rfl
    · rfl
  rw [he] at h
  exact h

end

end ShiReversibleGenerator
