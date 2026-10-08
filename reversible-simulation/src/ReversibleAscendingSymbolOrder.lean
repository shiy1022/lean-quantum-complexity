import ReversibleAscendingSymbolCellTraversal

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

/-- This reverses cell blocks, while retaining the separately specified order inside each block. -/
theorem ascendingSymbolCellPayload_reverse_range (capacity n count start : Nat) :
    ascendingSymbolCellPayload header stackRank symbolCard tm e backward ars capacity n count start =
      (List.range count).reverse.flatMap
        (fun j => symbolSequencePayload header stackRank symbolCard tm e backward ars capacity n (start + j)) := by
  induction count generalizing start with
  | zero => simp [ascendingSymbolCellPayload]
  | succ k ih =>
      rw [ascendingSymbolCellPayload, ih, List.range_succ_eq_map, List.reverse_cons,
        ← List.map_reverse, List.flatMap_append, List.flatMap_map]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Function.comp_def,
        Nat.succ_eq_add_one, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem ascendingSymbolCellTraversal_output_from_zero (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))
    (hi : s.counters (.inr 0) = 0) :
    (descendingResult (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s).output =
      (List.range count).reverse.flatMap
        (symbolSequencePayload header stackRank symbolCard tm e backward ars capacity n) ++ s.output := by
  rw [ascendingSymbolCellTraversal_output, hi, ascendingSymbolCellPayload_reverse_range]
  simp

end ShiReversibleGenerator
