import ReversibleInputComponent
import ReversibleAscendingInputComponent

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

theorem symbolCellTraversal_metadata (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))
    (r : WorkspaceRegister) :
    (descendingResult (symbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s).counters (.inl r) = s.counters (.inl r) := by
  induction count generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [descendingResult, ih]
      simp [symbolCellBody, symbolSequenceCounters_metadata]

theorem ascendingSymbolCellTraversal_metadata (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))
    (r : WorkspaceRegister) :
    (descendingResult (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s).counters (.inl r) = s.counters (.inl r) := by
  induction count generalizing s with
  | zero => rfl
  | succ k ih =>
      rw [descendingResult, ih]
      simp [ascendingSymbolCellBody, symbolSequenceCounters_metadata]

theorem inputComponentResult_metadata (n : Nat) (cs : InitializationRegister → Nat)
    (ys : List Bool) (r : WorkspaceRegister) :
    (inputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inl r) = cs (.inl r) := by
  simp [inputComponentResult, withCounter, symbolCellTraversal_metadata, inputComponentStartCfg, constantComponentStart]

theorem inputComponentResult_zero (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (inputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inr 0) = 0 := by
  simp [inputComponentResult, withCounter]

theorem inputComponentResult_output (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (inputComponentResult header stackRank symbolCard tm e backward ars n cs ys).output =
    (List.range (cs (.inl 2))).flatMap (symbolSequencePayload header stackRank symbolCard tm e backward ars (cs (.inl 2)) n) ++ ys := by
  simp [inputComponentResult, withCounter, symbolCellTraversal_output, inputComponentStartCfg, constantComponentStart]

theorem ascendingInputComponentResult_metadata (n : Nat) (cs : InitializationRegister → Nat)
    (ys : List Bool) (r : WorkspaceRegister) :
    (ascendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inl r) = cs (.inl r) := by
  simp [ascendingInputComponentResult, withCounter, ascendingSymbolCellTraversal_metadata, ascendingInputComponentStartCfg, ascendingConstantComponentStart]

theorem ascendingInputComponentResult_zero (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (ascendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inr 11) = 0 := by
  simp [ascendingInputComponentResult, withCounter]

theorem ascendingInputComponentResult_output (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (ascendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).output =
    ascendingSymbolCellPayload header stackRank symbolCard tm e backward ars (cs (.inl 2)) n (cs (.inl 2)) (cs (.inr 0)) ++ ys := by
  simp [ascendingInputComponentResult, withCounter, ascendingSymbolCellTraversal_output, ascendingInputComponentStartCfg, ascendingConstantComponentStart]

end ShiReversibleGenerator
