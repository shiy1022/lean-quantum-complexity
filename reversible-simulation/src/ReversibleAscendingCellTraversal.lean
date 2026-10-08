import ReversibleLocatedAscendingControl
import ReversibleLocatedCellTraversal

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard symbolRank : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (a : Option (MachineSymbol tm)) (backward : Bool)

noncomputable def ascendingCellBody (capacity n k : Nat) (s : CounterCfg InitializationRegister (LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward (Fin 4))) :
    CounterCfg InitializationRegister (LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward (Fin 4)) :=
  ⟨none, Function.update (locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward (Function.update s.counters (.inr 11) k)) (.inr 0) (s.counters (.inr 0) + 1),
    locatedCellPayload header stackRank symbolCard symbolRank tm e a backward capacity n (s.counters (.inr 0)) ++ s.output⟩

noncomputable def ascendingCellCost (k : Nat) (s : CounterCfg InitializationRegister (LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward (Fin 4))) :=
  locatedInitializationSteps header stackRank symbolCard symbolRank tm e a backward (Function.update s.counters (.inr 11) k) + 1

def ascendingCellInvariant (capacity n k : Nat) (s : CounterCfg InitializationRegister (LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward (Fin 4))) : Prop :=
  k ≤ capacity ∧ s.counters (.inr 0) + k = capacity ∧ s.counters (.inl 0) = n ∧
    s.counters (.inl 2) = capacity ∧ s.counters (.inl 6) = 0 ∧ s.counters (.inl 5) = 0

theorem ascendingCellBody_run (capacity n k : Nat) (s : CounterCfg InitializationRegister (LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward (Fin 4)))
    (hs : ascendingCellInvariant header stackRank symbolCard symbolRank tm e a backward capacity n (k + 1) s) :
    CounterRun (locatedAscendingCode header stackRank symbolCard symbolRank tm e a backward) (withCounter s (.inr 11) k (locatedInitializationEntry header stackRank symbolCard symbolRank tm e a backward))
      (ascendingCellCost header stackRank symbolCard symbolRank tm e a backward k s)
      (withCounter (ascendingCellBody header stackRank symbolCard symbolRank tm e a backward capacity n k s) (.inr 11) k (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0)) := by
  have hk : s.counters (.inr 0) < capacity := by have := hs.2.1; omega
  let cs := Function.update s.counters (Sum.inr 11 : InitializationRegister) k
  have h := locatedAscending_body header stackRank symbolCard symbolRank tm e a backward capacity n ⟨s.counters (.inr 0), hk⟩ cs
    (by simpa [cs] using hs.2.2.1) (by simp [cs])
    (by simpa [cs] using hs.2.2.2.2.1) (by simpa [cs] using hs.2.2.2.2.2) s.output
  have hc : Function.update (Function.update (locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs) (.inr 0) (s.counters (.inr 0) + 1)) (.inr 11) k =
      Function.update (locatedInitializationCounters header stackRank symbolCard symbolRank tm e a backward cs) (.inr 0) (s.counters (.inr 0) + 1) := by
    funext r
    by_cases hr : r = (Sum.inr 11 : InitializationRegister)
    · subst r
      simp [locatedInitialization_preserves_remaining, cs]
    · simp [hr]
  simpa [withCounter, ascendingCellBody, ascendingCellCost, locatedCellPayload, hk, cs,
    hs.2.2.2.1, hc] using h

theorem ascendingCellBody_invariant (capacity n k : Nat) (s : CounterCfg InitializationRegister (LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward (Fin 4)))
    (hs : ascendingCellInvariant header stackRank symbolCard symbolRank tm e a backward capacity n (k + 1) s) :
    ascendingCellInvariant header stackRank symbolCard symbolRank tm e a backward capacity n k (ascendingCellBody header stackRank symbolCard symbolRank tm e a backward capacity n k s) := by
  rcases hs with ⟨hk, hi, hn, hcap, hb, ht⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ascendingCellBody, Function.update_self]
    omega
  · simpa [ascendingCellBody, locatedInitialization_preserves_metadata] using hn
  · simpa [ascendingCellBody, locatedInitialization_preserves_metadata] using hcap
  · simpa [ascendingCellBody, locatedInitialization_preserves_metadata] using hb
  · simpa [ascendingCellBody, locatedInitialization_preserves_metadata] using ht

theorem ascendingCellTraversal_run (capacity n count : Nat) (s : CounterCfg InitializationRegister (LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward (Fin 4)))
    (hs : ascendingCellInvariant header stackRank symbolCard symbolRank tm e a backward capacity n count s) :
    CounterRun (locatedAscendingCode header stackRank symbolCard symbolRank tm e a backward) (withCounter s (.inr 11) count (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0))
      (descendingSteps (ascendingCellBody header stackRank symbolCard symbolRank tm e a backward capacity n) (ascendingCellCost header stackRank symbolCard symbolRank tm e a backward) count s)
      (withCounter (descendingResult (ascendingCellBody header stackRank symbolCard symbolRank tm e a backward capacity n) count s) (.inr 11) 0 (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 3)) := by
  exact descending_counter_run (locatedAscendingCode header stackRank symbolCard symbolRank tm e a backward) (.inr 11)
    (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 0) (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 1) (locatedInitializationEntry header stackRank symbolCard symbolRank tm e a backward) (locatedInitializationExit header stackRank symbolCard symbolRank tm e a backward 3)
    (locatedAscending_test header stackRank symbolCard symbolRank tm e a backward) (locatedAscending_pop header stackRank symbolCard symbolRank tm e a backward)
    (ascendingCellBody header stackRank symbolCard symbolRank tm e a backward capacity n) (ascendingCellCost header stackRank symbolCard symbolRank tm e a backward) (ascendingCellInvariant header stackRank symbolCard symbolRank tm e a backward capacity n)
    (ascendingCellBody_run header stackRank symbolCard symbolRank tm e a backward capacity n) (ascendingCellBody_invariant header stackRank symbolCard symbolRank tm e a backward capacity n) count s hs

/-- Prepending during ascending visits leaves the cell payloads in reverse order. -/
noncomputable def ascendingCellPayload (capacity n : Nat) : Nat → Nat → List Bool
  | 0, _ => []
  | count + 1, start => ascendingCellPayload capacity n count (start + 1) ++ locatedCellPayload header stackRank symbolCard symbolRank tm e a backward capacity n start

theorem ascendingCellTraversal_output (capacity n count : Nat) (s : CounterCfg InitializationRegister (LocatedInitializationLabels header stackRank symbolCard symbolRank tm e a backward (Fin 4))) :
    (descendingResult (ascendingCellBody header stackRank symbolCard symbolRank tm e a backward capacity n) count s).output =
      ascendingCellPayload header stackRank symbolCard symbolRank tm e a backward capacity n count (s.counters (.inr 0)) ++ s.output := by
  induction count generalizing s with
  | zero => simp [descendingResult, ascendingCellPayload]
  | succ k ih =>
      rw [descendingResult, ih]
      simp [ascendingCellBody, ascendingCellPayload, List.append_assoc]

end ShiReversibleGenerator
