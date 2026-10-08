import ReversibleSymbolAscendingControl
import ReversibleSymbolCellTraversal

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard : Nat)
    (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

noncomputable def ascendingSymbolCellBody (capacity n k : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4))) :
    CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)) :=
  ⟨none, Function.update (symbolSequenceCounters header stackRank symbolCard tm e backward ars (Function.update s.counters (.inr 11) k)) (.inr 0) (s.counters (.inr 0) + 1),
    symbolSequencePayload header stackRank symbolCard tm e backward ars capacity n (s.counters (.inr 0)) ++ s.output⟩

noncomputable def ascendingSymbolCellCost (k : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4))) :=
  symbolSequenceSteps header stackRank symbolCard tm e backward ars (Function.update s.counters (.inr 11) k) + 1

def ascendingSymbolCellInvariant (capacity n k : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4))) : Prop :=
  k ≤ capacity ∧ s.counters (.inr 0) + k = capacity ∧ s.counters (.inl 0) = n ∧
    s.counters (.inl 2) = capacity ∧ s.counters (.inl 6) = 0 ∧ s.counters (.inl 5) = 0

theorem ascendingSymbolCellBody_run (capacity n k : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))
    (hs : ascendingSymbolCellInvariant header stackRank symbolCard tm e backward ars capacity n (k + 1) s) :
    CounterRun (symbolAscendingCode header stackRank symbolCard tm e backward ars) (withCounter s (.inr 11) k (symbolSequenceEntry header stackRank symbolCard tm e backward ars 2))
      (ascendingSymbolCellCost header stackRank symbolCard tm e backward ars k s)
      (withCounter (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n k s) (.inr 11) k (symbolSequenceExit header stackRank symbolCard tm e backward ars 0)) := by
  have hk : s.counters (.inr 0) < capacity := by have := hs.2.1; omega
  let cs := Function.update s.counters (Sum.inr 11 : InitializationRegister) k
  have h := symbolAscending_body header stackRank symbolCard tm e backward ars capacity n ⟨s.counters (.inr 0), hk⟩ cs
    (by simpa [cs] using hs.2.2.1) (by simpa [cs] using hs.2.2.2.1) (by simp [cs])
    (by simpa [cs] using hs.2.2.2.2.1) (by simpa [cs] using hs.2.2.2.2.2) s.output
  have hc : Function.update (Function.update (symbolSequenceCounters header stackRank symbolCard tm e backward ars cs) (.inr 0) (s.counters (.inr 0) + 1)) (.inr 11) k =
      Function.update (symbolSequenceCounters header stackRank symbolCard tm e backward ars cs) (.inr 0) (s.counters (.inr 0) + 1) := by
    funext r
    by_cases hr : r = (Sum.inr 11 : InitializationRegister)
    · subst r
      simp [symbolSequenceCounters_remaining, cs]
    · simp [hr]
  simpa [withCounter, ascendingSymbolCellBody, ascendingSymbolCellCost, cs, hc] using h

theorem ascendingSymbolCellBody_invariant (capacity n k : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))
    (hs : ascendingSymbolCellInvariant header stackRank symbolCard tm e backward ars capacity n (k + 1) s) :
    ascendingSymbolCellInvariant header stackRank symbolCard tm e backward ars capacity n k (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n k s) := by
  rcases hs with ⟨hk, hi, hn, hcap, hb, ht⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ascendingSymbolCellBody, Function.update_self]
    omega
  · simpa [ascendingSymbolCellBody, symbolSequenceCounters_metadata] using hn
  · simpa [ascendingSymbolCellBody, symbolSequenceCounters_metadata] using hcap
  · simpa [ascendingSymbolCellBody, symbolSequenceCounters_metadata] using hb
  · simpa [ascendingSymbolCellBody, symbolSequenceCounters_metadata] using ht

theorem ascendingSymbolCellTraversal_run (capacity n count : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))
    (hs : ascendingSymbolCellInvariant header stackRank symbolCard tm e backward ars capacity n count s) :
    CounterRun (symbolAscendingCode header stackRank symbolCard tm e backward ars) (withCounter s (.inr 11) count (symbolSequenceExit header stackRank symbolCard tm e backward ars 0))
      (descendingSteps (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n) (ascendingSymbolCellCost header stackRank symbolCard tm e backward ars) count s)
      (withCounter (descendingResult (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s) (.inr 11) 0 (symbolSequenceExit header stackRank symbolCard tm e backward ars 3)) := by
  exact descending_counter_run (symbolAscendingCode header stackRank symbolCard tm e backward ars) (.inr 11)
    (symbolSequenceExit header stackRank symbolCard tm e backward ars 0) (symbolSequenceExit header stackRank symbolCard tm e backward ars 1) (symbolSequenceEntry header stackRank symbolCard tm e backward ars 2) (symbolSequenceExit header stackRank symbolCard tm e backward ars 3)
    (symbolAscending_test header stackRank symbolCard tm e backward ars) (symbolAscending_pop header stackRank symbolCard tm e backward ars)
    (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n) (ascendingSymbolCellCost header stackRank symbolCard tm e backward ars) (ascendingSymbolCellInvariant header stackRank symbolCard tm e backward ars capacity n)
    (ascendingSymbolCellBody_run header stackRank symbolCard tm e backward ars capacity n) (ascendingSymbolCellBody_invariant header stackRank symbolCard tm e backward ars capacity n) count s hs

/-- Prepending during ascending visits leaves the cell payloads in reverse order. -/
noncomputable def ascendingSymbolCellPayload (capacity n : Nat) : Nat → Nat → List Bool
  | 0, _ => []
  | count + 1, start => ascendingSymbolCellPayload capacity n count (start + 1) ++ symbolSequencePayload header stackRank symbolCard tm e backward ars capacity n start

theorem ascendingSymbolCellTraversal_output (capacity n count : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4))) :
    (descendingResult (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s).output =
      ascendingSymbolCellPayload header stackRank symbolCard tm e backward ars capacity n count (s.counters (.inr 0)) ++ s.output := by
  induction count generalizing s with
  | zero => simp [descendingResult, ascendingSymbolCellPayload]
  | succ k ih =>
      rw [descendingResult, ih]
      simp [ascendingSymbolCellBody, ascendingSymbolCellPayload, List.append_assoc]

theorem ascendingSymbolCellTraversal_index (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4))) :
    (descendingResult (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s).counters (.inr 0) =
      s.counters (.inr 0) + count := by
  induction count generalizing s with
  | zero => simp [descendingResult]
  | succ k ih =>
      rw [descendingResult, ih]
      simp [ascendingSymbolCellBody, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Incrementing the cell index leaves the independent layer count unchanged. -/
theorem ascendingSymbolCellTraversal_layer_bound (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4))) :
    (descendingResult (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s).counters (.inr 10) ≤
      s.counters (.inr 10) + count * (ars.length * 630) := by
  induction count generalizing s with
  | zero => simp [descendingResult]
  | succ k ih =>
      have h := ih (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n k s)
      have hb := symbolSequence_layer_bound header stackRank symbolCard tm e backward ars
        (Function.update s.counters (.inr 11) k)
      have hbase : (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n k s).counters (.inr 10) ≤
          s.counters (.inr 10) + ars.length * 630 := by
        simpa only [ascendingSymbolCellBody,
          Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 0),
          Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 11)] using hb
      simp only [descendingResult, Nat.succ_mul]
      omega

end ShiReversibleGenerator
