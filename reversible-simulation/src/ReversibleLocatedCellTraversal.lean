import ReversibleLocatedInitializationLoop

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool)

noncomputable def locatedCellPayload (capacity n k : Nat) : List Bool :=
  if hk : k < capacity then
    initializationCellPayload tm e capacity n ⟨k, hk⟩ a backward
      (n + 18 * (header + (stackRank * capacity + k) * symbolCard + symbolRank))
  else []

noncomputable def locatedCellBody (capacity n k : Nat) (s : CounterCfg InitializationRegister (LocatedCellLoopLabels header stackRank symbolCard symbolRank tm e a backward)) :
    CounterCfg InitializationRegister (LocatedCellLoopLabels header stackRank symbolCard symbolRank tm e a backward) :=
  ⟨none, locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward (Function.update s.counters (.inr 0) k),
    locatedCellPayload header stackRank symbolCard symbolRank tm e a backward capacity n k ++ s.output⟩

noncomputable def locatedCellCost (k : Nat) (s : CounterCfg InitializationRegister (LocatedCellLoopLabels header stackRank symbolCard symbolRank tm e a backward)) :=
  locatedInitializationSteps header stackRank symbolCard symbolRank tm e a backward (Function.update s.counters (.inr 0) k)

def locatedCellInvariant (capacity n k : Nat) (s : CounterCfg InitializationRegister (LocatedCellLoopLabels header stackRank symbolCard symbolRank tm e a backward)) : Prop :=
  k ≤ capacity ∧ s.counters (.inl 0) = n ∧ s.counters (.inl 2) = capacity ∧
    s.counters (.inl 6) = 0 ∧ s.counters (.inl 5) = 0

/-- The actual located printer implements each descending-loop body, including its bytes. -/
theorem locatedCellBody_run (capacity n k : Nat) (s : CounterCfg InitializationRegister (LocatedCellLoopLabels header stackRank symbolCard symbolRank tm e a backward))
    (hs : locatedCellInvariant header stackRank symbolCard symbolRank tm e a backward capacity n (k + 1) s) :
    CounterRun (locatedCellLoopCode header stackRank symbolCard symbolRank tm e a backward) (withCounter s (.inr 0) k (locatedInitializationEntry header stackRank symbolCard symbolRank tm e a backward))
      (locatedCellCost header stackRank symbolCard symbolRank tm e a backward k s)
      (withCounter (locatedCellBody header stackRank symbolCard symbolRank tm e a backward capacity n k s) (.inr 0) k (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0)) := by
  have hk : k < capacity := by have := hs.1; omega
  let cs := Function.update s.counters (Sum.inr 0 : InitializationRegister) k
  have h := locatedCellLoop_body header stackRank symbolCard symbolRank tm e a backward capacity n ⟨k, hk⟩ cs
    (by simpa [cs] using hs.2.1) (by simp [cs])
    (by simpa [cs] using hs.2.2.2.1) (by simpa [cs] using hs.2.2.2.2) s.output
  have hc : Function.update (locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs) (.inr 0) k = locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs := by
    funext r
    by_cases hr : r = (Sum.inr 0 : InitializationRegister)
    · subst r
      rw [Function.update_self, locatedInitialization_preserves_index]
      simp [cs]
    · simp [hr]
  simpa [withCounter, locatedCellBody, locatedCellCost, locatedCellPayload, hk,
    cs, hs.2.2.1, hc] using h

/-- Metadata and printer scratch stay valid for the next iteration. -/
theorem locatedCellBody_invariant (capacity n k : Nat) (s : CounterCfg InitializationRegister (LocatedCellLoopLabels header stackRank symbolCard symbolRank tm e a backward))
    (hs : locatedCellInvariant header stackRank symbolCard symbolRank tm e a backward capacity n (k + 1) s) :
    locatedCellInvariant header stackRank symbolCard symbolRank tm e a backward capacity n k (locatedCellBody header stackRank symbolCard symbolRank tm e a backward capacity n k s) := by
  rcases hs with ⟨hk, hn, hcap, hb, ht⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · simpa [locatedCellBody, locatedInitialization_preserves_metadata] using hn
  · simpa [locatedCellBody, locatedInitialization_preserves_metadata] using hcap
  · simpa [locatedCellBody, locatedInitialization_preserves_metadata] using hb
  · simpa [locatedCellBody, locatedInitialization_preserves_metadata] using ht

/-- A single fixed finite control graph visits every runtime cell, with an exact instruction count. -/
theorem locatedCellTraversal_run (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (LocatedCellLoopLabels header stackRank symbolCard symbolRank tm e a backward))
    (hs : locatedCellInvariant header stackRank symbolCard symbolRank tm e a backward capacity n count s) :
    CounterRun (locatedCellLoopCode header stackRank symbolCard symbolRank tm e a backward) (withCounter s (.inr 0) count (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0))
      (descendingSteps (locatedCellBody header stackRank symbolCard symbolRank tm e a backward capacity n) (locatedCellCost header stackRank symbolCard symbolRank tm e a backward) count s)
      (withCounter (descendingResult (locatedCellBody header stackRank symbolCard symbolRank tm e a backward capacity n) count s) (.inr 0) 0 (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 2)) := by
  exact descending_counter_run (locatedCellLoopCode header stackRank symbolCard symbolRank tm e a backward) (.inr 0)
    (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0) (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 1) (locatedInitializationEntry header stackRank symbolCard symbolRank tm e a backward) (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 2)
    (locatedCellLoop_test header stackRank symbolCard symbolRank tm e a backward) (locatedCellLoop_pop header stackRank symbolCard symbolRank tm e a backward)
    (locatedCellBody header stackRank symbolCard symbolRank tm e a backward capacity n) (locatedCellCost header stackRank symbolCard symbolRank tm e a backward)
    (locatedCellInvariant header stackRank symbolCard symbolRank tm e a backward capacity n)
    (locatedCellBody_run header stackRank symbolCard symbolRank tm e a backward capacity n) (locatedCellBody_invariant header stackRank symbolCard symbolRank tm e a backward capacity n) count s hs

/-- Since printing prepends, the descending execution leaves payloads in ascending cell order. -/
theorem locatedCellTraversal_output (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (LocatedCellLoopLabels header stackRank symbolCard symbolRank tm e a backward)) :
    (descendingResult (locatedCellBody header stackRank symbolCard symbolRank tm e a backward capacity n) count s).output =
      (List.range count).flatMap (locatedCellPayload header stackRank symbolCard symbolRank tm e a backward capacity n) ++ s.output := by
  induction count generalizing s with
  | zero => simp [descendingResult]
  | succ k ih =>
      rw [descendingResult, ih]
      simp [locatedCellBody, List.range_succ, List.flatMap_append, List.append_assoc]

end ShiReversibleGenerator
