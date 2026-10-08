import ReversibleAscendingConstantCellTraversal

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat)
    (backward : Bool) (ars : List (Bool × Nat))

/-- This reverses cell blocks, while retaining the separately specified order inside each block. -/
theorem ascendingConstantCellPayload_reverse_range (capacity n count start : Nat) :
    ascendingConstantCellPayload header stackRank symbolCard backward ars capacity n count start =
      (List.range count).reverse.flatMap
        (fun j => constantCellPayload header stackRank symbolCard backward ars capacity n (start + j)) := by
  induction count generalizing start with
  | zero => simp [ascendingConstantCellPayload]
  | succ k ih =>
      rw [ascendingConstantCellPayload, ih, List.range_succ_eq_map, List.reverse_cons,
        ← List.map_reverse, List.flatMap_append, List.flatMap_map]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Function.comp_def,
        Nat.succ_eq_add_one, Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem ascendingConstantCellTraversal_output_from_zero (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)))
    (hi : s.counters (.inr 0) = 0) :
    (descendingResult (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n) count s).output =
      (List.range count).reverse.flatMap
        (constantCellPayload header stackRank symbolCard backward ars capacity n) ++ s.output := by
  rw [ascendingConstantCellTraversal_output, hi, ascendingConstantCellPayload_reverse_range]
  simp

end ShiReversibleGenerator
