import ReversibleConstantAscendingControl

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat)
    (backward : Bool) (ars : List (Bool × Nat))

noncomputable def ascendingConstantCellBody (capacity n k : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4))) :
    CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)) :=
  ⟨none, Function.update (constantSequenceCounters header stackRank symbolCard backward ars (Function.update s.counters (.inr 11) k)) (.inr 0) (s.counters (.inr 0) + 1),
    constantCellPayload header stackRank symbolCard backward ars capacity n (s.counters (.inr 0)) ++ s.output⟩

noncomputable def ascendingConstantCellCost (k : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4))) :=
  constantSequenceSteps header stackRank symbolCard backward ars (Function.update s.counters (.inr 11) k) + 1

def ascendingConstantCellInvariant (capacity n k : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4))) : Prop :=
  k ≤ capacity ∧ s.counters (.inr 0) + k = capacity ∧ s.counters (.inl 0) = n ∧
    s.counters (.inl 2) = capacity ∧ s.counters (.inl 6) = 0 ∧ s.counters (.inl 5) = 0

theorem ascendingConstantCellBody_run (capacity n k : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)))
    (hs : ascendingConstantCellInvariant header stackRank symbolCard backward ars capacity n (k + 1) s) :
    CounterRun (constantAscendingCode header stackRank symbolCard backward ars) (withCounter s (.inr 11) k (constantSequenceEntry header stackRank symbolCard backward ars 2))
      (ascendingConstantCellCost header stackRank symbolCard backward ars k s)
      (withCounter (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n k s) (.inr 11) k (constantSequenceExit header stackRank symbolCard backward ars 0)) := by
  let cs := Function.update s.counters (Sum.inr 11 : InitializationRegister) k
  have h := constantAscending_body header stackRank symbolCard backward ars cs
    (by simpa [cs] using hs.2.2.2.2.1) (by simpa [cs] using hs.2.2.2.2.2) s.output
  rw [constantSequencePayload_eq header stackRank symbolCard backward ars capacity n (s.counters (.inr 0)) cs
    (by simpa [cs] using hs.2.2.1) (by simpa [cs] using hs.2.2.2.1) (by simp [cs])] at h
  have hc : Function.update (Function.update (constantSequenceCounters header stackRank symbolCard backward ars cs) (.inr 0) (s.counters (.inr 0) + 1)) (.inr 11) k =
      Function.update (constantSequenceCounters header stackRank symbolCard backward ars cs) (.inr 0) (s.counters (.inr 0) + 1) := by
    funext r
    by_cases hr : r = (Sum.inr 11 : InitializationRegister)
    · subst r
      simp [constantSequenceCounters_remaining, cs]
    · simp [hr]
  simpa [withCounter, ascendingConstantCellBody, ascendingConstantCellCost, cs, hc] using h

theorem ascendingConstantCellBody_invariant (capacity n k : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)))
    (hs : ascendingConstantCellInvariant header stackRank symbolCard backward ars capacity n (k + 1) s) :
    ascendingConstantCellInvariant header stackRank symbolCard backward ars capacity n k (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n k s) := by
  rcases hs with ⟨hk, hi, hn, hcap, hb, ht⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ascendingConstantCellBody, Function.update_self]
    omega
  · simpa [ascendingConstantCellBody, constantSequenceCounters_metadata] using hn
  · simpa [ascendingConstantCellBody, constantSequenceCounters_metadata] using hcap
  · simpa [ascendingConstantCellBody, constantSequenceCounters_metadata] using hb
  · simpa [ascendingConstantCellBody, constantSequenceCounters_metadata] using ht

theorem ascendingConstantCellTraversal_run (capacity n count : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4)))
    (hs : ascendingConstantCellInvariant header stackRank symbolCard backward ars capacity n count s) :
    CounterRun (constantAscendingCode header stackRank symbolCard backward ars) (withCounter s (.inr 11) count (constantSequenceExit header stackRank symbolCard backward ars 0))
      (descendingSteps (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n) (ascendingConstantCellCost header stackRank symbolCard backward ars) count s)
      (withCounter (descendingResult (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n) count s) (.inr 11) 0 (constantSequenceExit header stackRank symbolCard backward ars 3)) := by
  exact descending_counter_run (constantAscendingCode header stackRank symbolCard backward ars) (.inr 11)
    (constantSequenceExit header stackRank symbolCard backward ars 0) (constantSequenceExit header stackRank symbolCard backward ars 1) (constantSequenceEntry header stackRank symbolCard backward ars 2) (constantSequenceExit header stackRank symbolCard backward ars 3)
    (constantAscending_test header stackRank symbolCard backward ars) (constantAscending_pop header stackRank symbolCard backward ars)
    (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n) (ascendingConstantCellCost header stackRank symbolCard backward ars) (ascendingConstantCellInvariant header stackRank symbolCard backward ars capacity n)
    (ascendingConstantCellBody_run header stackRank symbolCard backward ars capacity n) (ascendingConstantCellBody_invariant header stackRank symbolCard backward ars capacity n) count s hs

/-- Prepending during ascending visits leaves the cell payloads in reverse order. -/
noncomputable def ascendingConstantCellPayload (capacity n : Nat) : Nat → Nat → List Bool
  | 0, _ => []
  | count + 1, start => ascendingConstantCellPayload capacity n count (start + 1) ++ constantCellPayload header stackRank symbolCard backward ars capacity n start

theorem ascendingConstantCellTraversal_output (capacity n count : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4))) :
    (descendingResult (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n) count s).output =
      ascendingConstantCellPayload header stackRank symbolCard backward ars capacity n count (s.counters (.inr 0)) ++ s.output := by
  induction count generalizing s with
  | zero => simp [descendingResult, ascendingConstantCellPayload]
  | succ k ih =>
      rw [descendingResult, ih]
      simp [ascendingConstantCellBody, ascendingConstantCellPayload, List.append_assoc]

theorem ascendingConstantCellTraversal_index (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4))) :
    (descendingResult (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n) count s).counters (.inr 0) =
      s.counters (.inr 0) + count := by
  induction count generalizing s with
  | zero => simp [descendingResult]
  | succ k ih =>
      rw [descendingResult, ih]
      simp [ascendingConstantCellBody, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]


end ShiReversibleGenerator
