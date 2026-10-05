import «BQP-counting-threshold»

set_option maxRecDepth 30000
set_option maxHeartbeats 40000000

open Lean Elab Command in
run_cmd do
  let names := #[
    ``BQPCounting.count_le,
    ``BQPCounting.gap_complement,
    ``BQPCounting.gap_first_bit,
    ``BQPCounting.gap_suffix,
    ``BQPCounting.combinedChecker,
    ``BQPCounting.combined_gap,
    ``BQPCounting.coefficient,
    ``BQPCounting.combined_gap_counts,
    ``BQPCounting.coefficient_bound,
    ``BQPCounting.integer_sign,
    ``BQPCounting.combined_gap_positive_iff,
    ``BQPCounting.gap_pos_iff_majority,
    ``BQPCounting.exists_long_budget,
    ``BQPCounting.long_majority,
    ``BQPCounting.shortChecker,
    ``BQPCounting.patched_majority]
  for name in names do
    let axs ← liftCoreM (collectAxioms name)
    for ax in axs do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    logInfo m!"BQP_COUNTING_CHECKED {name}; axioms {axs}"

-- The router formula is nonvacuous at a realizable budget and remains stable
-- under extra suffix bits (the unused buckets use its balanced head-bit branch).
example (N : ℕ) (hN : 10 ≤ N) :
    ShiClassPP.gap
      (BQPCounting.combinedChecker (fun _ => 1) (fun _ _ => false)) [false, false] N = -64 := by
  rw [BQPCounting.combined_gap (fun _ => 1) (fun _ _ => false)
    [false, false] N (by decide) hN]
  norm_num

example : 3 * (1 : ℕ) + 7 ≤ ([false, false] : List Bool).length ^ 4 := by decide
