import ReversibleConstantSequenceControl

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

noncomputable def constantCellBody (capacity n k : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3))) :
    CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)) :=
  ⟨none, constantSequenceCounters header stackRank symbolCard backward ars (Function.update s.counters (.inr 0) k), constantCellPayload header stackRank symbolCard backward ars capacity n k ++ s.output⟩

noncomputable def constantCellCost (k : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3))) :=
  constantSequenceSteps header stackRank symbolCard backward ars (Function.update s.counters (.inr 0) k)

def constantCellInvariant (capacity n k : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3))) : Prop :=
  k ≤ capacity ∧ s.counters (.inl 0) = n ∧ s.counters (.inl 2) = capacity ∧
    s.counters (.inl 6) = 0 ∧ s.counters (.inl 5) = 0

/-- All symbols are dispatched inside the runtime cell iteration. -/
theorem constantCellBody_run (capacity n k : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)))
    (hs : constantCellInvariant header stackRank symbolCard backward ars capacity n (k + 1) s) :
    CounterRun (constantCellLoopCode header stackRank symbolCard backward ars) (withCounter s (.inr 0) k (constantSequenceEntry header stackRank symbolCard backward ars 0)) (constantCellCost header stackRank symbolCard backward ars k s)
      (withCounter (constantCellBody header stackRank symbolCard backward ars capacity n k s) (.inr 0) k (constantSequenceExit header stackRank symbolCard backward ars 0)) := by
  classical
  let cs := Function.update s.counters (Sum.inr 0 : InitializationRegister) k
  have h := constantSequence_run header stackRank symbolCard backward ars (fun (_ : Fin 3) => .halt) 0 cs
    (by simpa [cs] using hs.2.2.2.1) (by simpa [cs] using hs.2.2.2.2) s.output
  rw [constantSequencePayload_eq header stackRank symbolCard backward ars capacity n k cs
    (by simpa [cs] using hs.2.1) (by simpa [cs] using hs.2.2.1) (by simp [cs])] at h
  have hh : ∀ (l : Fin 3), constantSequenceCode header stackRank symbolCard backward ars (fun (_ : Fin 3) => .halt) 0 (constantSequenceExit header stackRank symbolCard backward ars l) = .halt := by
    intro l
    rw [constantSequenceCode_embed]
    rfl
  have h' := reentryCode_preserves_run _ (.inr 0)
    (constantSequenceExit header stackRank symbolCard backward ars 0) (constantSequenceExit header stackRank symbolCard backward ars 1)
    (constantSequenceEntry header stackRank symbolCard backward ars 0) (constantSequenceExit header stackRank symbolCard backward ars 2) (hh 0) (hh 1) h (by simp)
  have hc : Function.update (constantSequenceCounters header stackRank symbolCard backward ars cs) (.inr 0) k = constantSequenceCounters header stackRank symbolCard backward ars cs := by
    funext r
    by_cases hr : r = (Sum.inr 0 : InitializationRegister)
    · subst r
      rw [Function.update_self, constantSequenceCounters_index]
      simp [cs]
    · simp [hr]
  simpa [constantCellLoopCode, withCounter, constantCellBody, constantCellCost, cs, hc] using h'

theorem constantCellBody_invariant (capacity n k : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)))
    (hs : constantCellInvariant header stackRank symbolCard backward ars capacity n (k + 1) s) :
    constantCellInvariant header stackRank symbolCard backward ars capacity n k (constantCellBody header stackRank symbolCard backward ars capacity n k s) := by
  rcases hs with ⟨hk, hn, hcap, hb, ht⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · simpa [constantCellBody, constantSequenceCounters_metadata] using hn
  · simpa [constantCellBody, constantSequenceCounters_metadata] using hcap
  · simpa [constantCellBody, constantSequenceCounters_metadata] using hb
  · simpa [constantCellBody, constantSequenceCounters_metadata] using ht

/-- Full counted cell traversal with finite symbol dispatch at every cell. -/
theorem constantCellTraversal_run (capacity n count : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3)))
    (hs : constantCellInvariant header stackRank symbolCard backward ars capacity n count s) :
    CounterRun (constantCellLoopCode header stackRank symbolCard backward ars) (withCounter s (.inr 0) count (constantSequenceExit header stackRank symbolCard backward ars 0))
      (descendingSteps (constantCellBody header stackRank symbolCard backward ars capacity n) (constantCellCost header stackRank symbolCard backward ars) count s)
      (withCounter (descendingResult (constantCellBody header stackRank symbolCard backward ars capacity n) count s) (.inr 0) 0 (constantSequenceExit header stackRank symbolCard backward ars 2)) := by
  exact descending_counter_run (constantCellLoopCode header stackRank symbolCard backward ars) (.inr 0) (constantSequenceExit header stackRank symbolCard backward ars 0) (constantSequenceExit header stackRank symbolCard backward ars 1) (constantSequenceEntry header stackRank symbolCard backward ars 0) (constantSequenceExit header stackRank symbolCard backward ars 2)
    (constantCellLoop_test header stackRank symbolCard backward ars) (constantCellLoop_pop header stackRank symbolCard backward ars)
    (constantCellBody header stackRank symbolCard backward ars capacity n) (constantCellCost header stackRank symbolCard backward ars) (constantCellInvariant header stackRank symbolCard backward ars capacity n)
    (constantCellBody_run header stackRank symbolCard backward ars capacity n) (constantCellBody_invariant header stackRank symbolCard backward ars capacity n) count s hs


theorem constantCellTraversal_output (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3))) :
    (descendingResult (constantCellBody header stackRank symbolCard backward ars capacity n) count s).output =
      (List.range count).flatMap (constantCellPayload header stackRank symbolCard backward ars capacity n) ++ s.output := by
  induction count generalizing s with
  | zero => simp [descendingResult]
  | succ k ih =>
      rw [descendingResult, ih]
      simp [constantCellBody, List.range_succ, List.flatMap_append, List.append_assoc]

end ShiReversibleGenerator
