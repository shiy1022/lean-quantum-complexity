import ReversibleInputComponentClock
import ReversibleConstantTraversalResult

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

theorem symbolCellTraversal_final_budget (bound layers capacity n count : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))
    (hb : ∀ ar ∈ ars, n + 18 * (header + (stackRank * capacity + capacity) * symbolCard + ar.2) + 18 ≤ bound)
    (hs : SymbolCellBudgetInvariant header stackRank symbolCard tm e backward ars bound layers capacity n count s) :
    CounterBudget (descendingResult (symbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s).counters
      (.inr 10) bound := by
  have h := descendingResult_invariant
    (symbolCellBody header stackRank symbolCard tm e backward ars capacity n)
    (SymbolCellBudgetInvariant header stackRank symbolCard tm e backward ars bound layers capacity n)
    (fun k t ht => symbolCellBudget_next header stackRank symbolCard tm e backward ars bound layers capacity n k t hb ht)
    count s hs
  exact h.2.1

theorem ascendingSymbolCellTraversal_final_budget (bound layers capacity n count : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))
    (hb : ∀ ar ∈ ars, n + 18 * (header + (stackRank * capacity + capacity) * symbolCard + ar.2) + 18 ≤ bound)
    (hs : AscendingSymbolBudgetInvariant header stackRank symbolCard tm e backward ars bound layers capacity n count s) :
    CounterBudget (descendingResult (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s).counters
      (.inr 10) bound := by
  have h := descendingResult_invariant
    (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n)
    (AscendingSymbolBudgetInvariant header stackRank symbolCard tm e backward ars bound layers capacity n)
    (fun k t ht => ascendingSymbolBudget_next header stackRank symbolCard tm e backward ars bound layers capacity n k t hb ht)
    count s hs
  exact h.2.1

theorem inputComponentResult_layer_bound (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (inputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inr 10) ≤
      cs (.inr 10) + cs (.inl 2) * (ars.length * 630) := by
  simpa [inputComponentResult, withCounter, inputComponentStartCfg, constantComponentStart] using
    symbolCellTraversal_layer_bound header stackRank symbolCard tm e backward ars (cs (.inl 2)) n (cs (.inl 2)) (inputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys)

theorem inputComponentResult_budget (n bound layers : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (hbudget : CounterBudget cs (.inr 10) bound) (hl : cs (.inr 10) ≤ layers)
    (haddr : ∀ ar ∈ ars, n + 18 * (header + (stackRank * cs (.inl 2) + cs (.inl 2)) * symbolCard + ar.2) + 18 ≤ bound)
    (ys : List Bool) :
    CounterBudget (inputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inr 10) bound := by
  have hs := inputComponentStart_budget header stackRank symbolCard tm e backward ars n bound layers cs hn hb ht hbudget hl ys
  have h := symbolCellTraversal_final_budget header stackRank symbolCard tm e backward ars bound layers (cs (.inl 2)) n (cs (.inl 2))
    (inputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys) haddr hs
  exact h.update (.inr 0) 0 (Nat.zero_le bound)

theorem ascendingInputComponentResult_layer_bound (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (ascendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inr 10) ≤
      cs (.inr 10) + cs (.inl 2) * (ars.length * 630) := by
  simpa [ascendingInputComponentResult, withCounter, ascendingInputComponentStartCfg, ascendingConstantComponentStart] using
    ascendingSymbolCellTraversal_layer_bound header stackRank symbolCard tm e backward ars (cs (.inl 2)) n (cs (.inl 2)) (ascendingInputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys)

theorem ascendingInputComponentResult_budget (n bound layers : Nat) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = 0) (hb : cs (.inl 6) = 0) (ht : cs (.inl 5) = 0)
    (hbudget : CounterBudget cs (.inr 10) bound) (hl : cs (.inr 10) ≤ layers)
    (haddr : ∀ ar ∈ ars, n + 18 * (header + (stackRank * cs (.inl 2) + cs (.inl 2)) * symbolCard + ar.2) + 18 ≤ bound)
    (ys : List Bool) :
    CounterBudget (ascendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inr 10) bound := by
  have hs := ascendingInputComponentStart_budget header stackRank symbolCard tm e backward ars n bound layers cs hn hi hb ht hbudget hl ys
  have h := ascendingSymbolCellTraversal_final_budget header stackRank symbolCard tm e backward ars bound layers (cs (.inl 2)) n (cs (.inl 2))
    (ascendingInputComponentStartCfg header stackRank symbolCard tm e backward ars cs ys) haddr hs
  exact h.update (.inr 11) 0 (Nat.zero_le bound)

end ShiReversibleGenerator
