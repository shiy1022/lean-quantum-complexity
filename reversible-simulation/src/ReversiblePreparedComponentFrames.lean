import ReversiblePreparedConstantComponents
import ReversiblePreparedInputComponents
import ReversibleConstantComponentResultBudget
import ReversibleInputComponentResultBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM

section
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

theorem preparedConstantComponentResult_metadata (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) (r : WorkspaceRegister) :
    (preparedConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inl r) = cs (.inl r) := by
  simp only [preparedConstantComponentResult, CounterCfg.relabel, constantComponentResult_metadata, initializationLoopReset_metadata]

theorem preparedConstantComponentResult_output (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedConstantComponentResult header stackRank symbolCard backward ars n cs ys).output = (List.range (cs (.inl 2))).flatMap (constantCellPayload header stackRank symbolCard backward ars (cs (.inl 2)) n) ++ ys := by
  simp only [preparedConstantComponentResult, CounterCfg.relabel, constantComponentResult_output, initializationLoopReset_metadata, initializationLoopReset_index]

theorem preparedConstantComponent_exit :
    preparedConstantComponentCode header stackRank symbolCard backward ars (cleanupExit initializationLoopReset (.inr (.inr (constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 3))) : AffineLabel 0 1 (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)))) = .halt := by
  rw [preparedConstantComponentCode, cleanupCode_embed]
  rw [constantComponent_exit]
  rfl

theorem preparedConstantComponentResult_pc (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedConstantComponentResult header stackRank symbolCard backward ars n cs ys).pc = some (cleanupExit initializationLoopReset (.inr (.inr (constantSequenceExit header stackRank symbolCard backward ars (2 : Fin 3))) : AffineLabel 0 1 (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)))) := rfl

theorem preparedConstantComponentResult_layer_bound (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inr 10) ≤ cs (.inr 10) + cs (.inl 2) * (ars.length * 630) := by
  simpa only [preparedConstantComponentResult, CounterCfg.relabel, initializationLoopReset_layers, initializationLoopReset_metadata] using
    constantComponentResult_layer_bound header stackRank symbolCard backward ars n (cleanupCounters initializationLoopReset cs) ys

theorem preparedConstantComponentResult_budget (n bound layers : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (hbudget : CounterBudget cs (.inr 10) bound) (hl : cs (.inr 10) ≤ layers)
    (haddr : ∀ ar ∈ ars, n + 18 * (header + (stackRank * cs (.inl 2) + cs (.inl 2)) * symbolCard + ar.2) + 18 ≤ bound)
    (ys : List Bool) :
    CounterBudget (preparedConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inr 10) bound := by
  have h := constantComponentResult_budget header stackRank symbolCard backward ars n bound layers (cleanupCounters initializationLoopReset cs)
    (by simpa only [initializationLoopReset_metadata] using hn)
    (by simpa only [initializationLoopReset_metadata] using hb)
    (by simpa only [initializationLoopReset_metadata] using ht)
    (initializationLoopReset_budget cs bound hbudget)
    (by simpa only [initializationLoopReset_layers] using hl)
    (by simpa only [initializationLoopReset_metadata] using haddr) ys
  simpa only [preparedConstantComponentResult, CounterCfg.relabel] using h

theorem preparedAscendingConstantComponentResult_metadata (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) (r : WorkspaceRegister) :
    (preparedAscendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inl r) = cs (.inl r) := by
  simp only [preparedAscendingConstantComponentResult, CounterCfg.relabel, ascendingConstantComponentResult_metadata, initializationLoopReset_metadata]

theorem preparedAscendingConstantComponentResult_output (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedAscendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).output = ascendingConstantCellPayload header stackRank symbolCard backward ars (cs (.inl 2)) n (cs (.inl 2)) 0 ++ ys := by
  simp only [preparedAscendingConstantComponentResult, CounterCfg.relabel, ascendingConstantComponentResult_output, initializationLoopReset_metadata, initializationLoopReset_index]

theorem preparedAscendingConstantComponent_exit :
    preparedAscendingConstantComponentCode header stackRank symbolCard backward ars (cleanupExit initializationLoopReset (.inr (.inr (constantSequenceExit header stackRank symbolCard backward ars (3 : Fin 4))) : AffineLabel 0 1 (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)))) = .halt := by
  rw [preparedAscendingConstantComponentCode, cleanupCode_embed]
  rw [ascendingConstantComponent_exit]
  rfl

theorem preparedAscendingConstantComponentResult_pc (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedAscendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).pc = some (cleanupExit initializationLoopReset (.inr (.inr (constantSequenceExit header stackRank symbolCard backward ars (3 : Fin 4))) : AffineLabel 0 1 (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)))) := rfl

theorem preparedAscendingConstantComponentResult_layer_bound (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedAscendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inr 10) ≤ cs (.inr 10) + cs (.inl 2) * (ars.length * 630) := by
  simpa only [preparedAscendingConstantComponentResult, CounterCfg.relabel, initializationLoopReset_layers, initializationLoopReset_metadata] using
    ascendingConstantComponentResult_layer_bound header stackRank symbolCard backward ars n (cleanupCounters initializationLoopReset cs) ys

theorem preparedAscendingConstantComponentResult_budget (n bound layers : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (hbudget : CounterBudget cs (.inr 10) bound) (hl : cs (.inr 10) ≤ layers)
    (haddr : ∀ ar ∈ ars, n + 18 * (header + (stackRank * cs (.inl 2) + cs (.inl 2)) * symbolCard + ar.2) + 18 ≤ bound)
    (ys : List Bool) :
    CounterBudget (preparedAscendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inr 10) bound := by
  have h := ascendingConstantComponentResult_budget header stackRank symbolCard backward ars n bound layers (cleanupCounters initializationLoopReset cs)
    (by simpa only [initializationLoopReset_metadata] using hn)
    (initializationLoopReset_index cs)
    (by simpa only [initializationLoopReset_metadata] using hb)
    (by simpa only [initializationLoopReset_metadata] using ht)
    (initializationLoopReset_budget cs bound hbudget)
    (by simpa only [initializationLoopReset_layers] using hl)
    (by simpa only [initializationLoopReset_metadata] using haddr) ys
  simpa only [preparedAscendingConstantComponentResult, CounterCfg.relabel] using h

end

section
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

theorem preparedInputComponentResult_metadata (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) (r : WorkspaceRegister) :
    (preparedInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inl r) = cs (.inl r) := by
  simp only [preparedInputComponentResult, CounterCfg.relabel, inputComponentResult_metadata, initializationLoopReset_metadata]

theorem preparedInputComponentResult_output (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).output = (List.range (cs (.inl 2))).flatMap (symbolSequencePayload header stackRank symbolCard tm e backward ars (cs (.inl 2)) n) ++ ys := by
  simp only [preparedInputComponentResult, CounterCfg.relabel, inputComponentResult_output, initializationLoopReset_metadata, initializationLoopReset_index]

theorem preparedInputComponent_exit :
    preparedInputComponentCode header stackRank symbolCard tm e backward ars (cleanupExit initializationLoopReset (.inr (.inr (symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 3))) : AffineLabel 0 1 (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))) = .halt := by
  rw [preparedInputComponentCode, cleanupCode_embed]
  rw [inputComponent_exit]
  rfl

theorem preparedInputComponentResult_pc (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).pc = some (cleanupExit initializationLoopReset (.inr (.inr (symbolSequenceExit header stackRank symbolCard tm e backward ars (2 : Fin 3))) : AffineLabel 0 1 (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))) := rfl

theorem preparedInputComponentResult_layer_bound (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inr 10) ≤ cs (.inr 10) + cs (.inl 2) * (ars.length * 630) := by
  simpa only [preparedInputComponentResult, CounterCfg.relabel, initializationLoopReset_layers, initializationLoopReset_metadata] using
    inputComponentResult_layer_bound header stackRank symbolCard tm e backward ars n (cleanupCounters initializationLoopReset cs) ys

theorem preparedInputComponentResult_budget (n bound layers : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (hbudget : CounterBudget cs (.inr 10) bound) (hl : cs (.inr 10) ≤ layers)
    (haddr : ∀ ar ∈ ars, n + 18 * (header + (stackRank * cs (.inl 2) + cs (.inl 2)) * symbolCard + ar.2) + 18 ≤ bound)
    (ys : List Bool) :
    CounterBudget (preparedInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inr 10) bound := by
  have h := inputComponentResult_budget header stackRank symbolCard tm e backward ars n bound layers (cleanupCounters initializationLoopReset cs)
    (by simpa only [initializationLoopReset_metadata] using hn)
    (by simpa only [initializationLoopReset_metadata] using hb)
    (by simpa only [initializationLoopReset_metadata] using ht)
    (initializationLoopReset_budget cs bound hbudget)
    (by simpa only [initializationLoopReset_layers] using hl)
    (by simpa only [initializationLoopReset_metadata] using haddr) ys
  simpa only [preparedInputComponentResult, CounterCfg.relabel] using h

theorem preparedAscendingInputComponentResult_metadata (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) (r : WorkspaceRegister) :
    (preparedAscendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inl r) = cs (.inl r) := by
  simp only [preparedAscendingInputComponentResult, CounterCfg.relabel, ascendingInputComponentResult_metadata, initializationLoopReset_metadata]

theorem preparedAscendingInputComponentResult_output (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedAscendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).output = ascendingSymbolCellPayload header stackRank symbolCard tm e backward ars (cs (.inl 2)) n (cs (.inl 2)) 0 ++ ys := by
  simp only [preparedAscendingInputComponentResult, CounterCfg.relabel, ascendingInputComponentResult_output, initializationLoopReset_metadata, initializationLoopReset_index]

theorem preparedAscendingInputComponent_exit :
    preparedAscendingInputComponentCode header stackRank symbolCard tm e backward ars (cleanupExit initializationLoopReset (.inr (.inr (symbolSequenceExit header stackRank symbolCard tm e backward ars (3 : Fin 4))) : AffineLabel 0 1 (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))) = .halt := by
  rw [preparedAscendingInputComponentCode, cleanupCode_embed]
  rw [ascendingInputComponent_exit]
  rfl

theorem preparedAscendingInputComponentResult_pc (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedAscendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).pc = some (cleanupExit initializationLoopReset (.inr (.inr (symbolSequenceExit header stackRank symbolCard tm e backward ars (3 : Fin 4))) : AffineLabel 0 1 (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))) := rfl

theorem preparedAscendingInputComponentResult_layer_bound (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedAscendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inr 10) ≤ cs (.inr 10) + cs (.inl 2) * (ars.length * 630) := by
  simpa only [preparedAscendingInputComponentResult, CounterCfg.relabel, initializationLoopReset_layers, initializationLoopReset_metadata] using
    ascendingInputComponentResult_layer_bound header stackRank symbolCard tm e backward ars n (cleanupCounters initializationLoopReset cs) ys

theorem preparedAscendingInputComponentResult_budget (n bound layers : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (hbudget : CounterBudget cs (.inr 10) bound) (hl : cs (.inr 10) ≤ layers)
    (haddr : ∀ ar ∈ ars, n + 18 * (header + (stackRank * cs (.inl 2) + cs (.inl 2)) * symbolCard + ar.2) + 18 ≤ bound)
    (ys : List Bool) :
    CounterBudget (preparedAscendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inr 10) bound := by
  have h := ascendingInputComponentResult_budget header stackRank symbolCard tm e backward ars n bound layers (cleanupCounters initializationLoopReset cs)
    (by simpa only [initializationLoopReset_metadata] using hn)
    (initializationLoopReset_index cs)
    (by simpa only [initializationLoopReset_metadata] using hb)
    (by simpa only [initializationLoopReset_metadata] using ht)
    (initializationLoopReset_budget cs bound hbudget)
    (by simpa only [initializationLoopReset_layers] using hl)
    (by simpa only [initializationLoopReset_metadata] using haddr) ys
  simpa only [preparedAscendingInputComponentResult, CounterCfg.relabel] using h

end

end ShiReversibleGenerator
