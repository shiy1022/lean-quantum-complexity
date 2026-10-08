import ReversibleInitializationLayerBound

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

noncomputable def symbolCellLoopCode : (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)) → CounterInstr InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)) := by
  classical
  exact reentryCode (symbolSequenceCode header stackRank symbolCard tm e backward ars (fun (_ : Fin 3) => .halt) 0) (.inr 0) (symbolSequenceExit header stackRank symbolCard tm e backward ars 0) (symbolSequenceExit header stackRank symbolCard tm e backward ars 1) (symbolSequenceEntry header stackRank symbolCard tm e backward ars 0) (symbolSequenceExit header stackRank symbolCard tm e backward ars 2)

theorem symbolCellLoop_test : symbolCellLoopCode header stackRank symbolCard tm e backward ars (symbolSequenceExit header stackRank symbolCard tm e backward ars 0) = .branch (.inr 0) (symbolSequenceExit header stackRank symbolCard tm e backward ars 2) (symbolSequenceExit header stackRank symbolCard tm e backward ars 1) := by
  classical
  exact reentryCode_loop _ _ _ _ _ _

theorem symbolCellLoop_pop : symbolCellLoopCode header stackRank symbolCard tm e backward ars (symbolSequenceExit header stackRank symbolCard tm e backward ars 1) = .dec (.inr 0) (symbolSequenceEntry header stackRank symbolCard tm e backward ars 0) := by
  classical
  apply reentryCode_pop
  intro h
  exact (by decide : (1 : Fin 3) ≠ 0) (symbolSequenceExit_injective header stackRank symbolCard tm e backward ars h)

noncomputable def symbolCellBody (capacity n k : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3))) :
    CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)) :=
  ⟨none, symbolSequenceCounters header stackRank symbolCard tm e backward ars (Function.update s.counters (.inr 0) k), symbolSequencePayload header stackRank symbolCard tm e backward ars capacity n k ++ s.output⟩

noncomputable def symbolCellCost (k : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3))) :=
  symbolSequenceSteps header stackRank symbolCard tm e backward ars (Function.update s.counters (.inr 0) k)

def symbolCellInvariant (capacity n k : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3))) : Prop :=
  k ≤ capacity ∧ s.counters (.inl 0) = n ∧ s.counters (.inl 2) = capacity ∧
    s.counters (.inl 6) = 0 ∧ s.counters (.inl 5) = 0

/-- All symbols are dispatched inside the runtime cell iteration. -/
theorem symbolCellBody_run (capacity n k : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))
    (hs : symbolCellInvariant header stackRank symbolCard tm e backward ars capacity n (k + 1) s) :
    CounterRun (symbolCellLoopCode header stackRank symbolCard tm e backward ars) (withCounter s (.inr 0) k (symbolSequenceEntry header stackRank symbolCard tm e backward ars 0)) (symbolCellCost header stackRank symbolCard tm e backward ars k s)
      (withCounter (symbolCellBody header stackRank symbolCard tm e backward ars capacity n k s) (.inr 0) k (symbolSequenceExit header stackRank symbolCard tm e backward ars 0)) := by
  classical
  have hk : k < capacity := by have := hs.1; omega
  let cs := Function.update s.counters (Sum.inr 0 : InitializationRegister) k
  have h := symbolSequence_run header stackRank symbolCard tm e backward ars (fun (_ : Fin 3) => .halt) 0 capacity n ⟨k, hk⟩ cs
    (by simpa [cs] using hs.2.1) (by simpa [cs] using hs.2.2.1) (by simp [cs])
    (by simpa [cs] using hs.2.2.2.1) (by simpa [cs] using hs.2.2.2.2) s.output
  have hh : ∀ (l : Fin 3), symbolSequenceCode header stackRank symbolCard tm e backward ars (fun (_ : Fin 3) => .halt) 0 (symbolSequenceExit header stackRank symbolCard tm e backward ars l) = .halt := by
    intro l
    rw [symbolSequenceCode_embed]
    rfl
  have h' := reentryCode_preserves_run _ (.inr 0)
    (symbolSequenceExit header stackRank symbolCard tm e backward ars 0) (symbolSequenceExit header stackRank symbolCard tm e backward ars 1)
    (symbolSequenceEntry header stackRank symbolCard tm e backward ars 0) (symbolSequenceExit header stackRank symbolCard tm e backward ars 2) (hh 0) (hh 1) h (by simp)
  have hc : Function.update (symbolSequenceCounters header stackRank symbolCard tm e backward ars cs) (.inr 0) k = symbolSequenceCounters header stackRank symbolCard tm e backward ars cs := by
    funext r
    by_cases hr : r = (Sum.inr 0 : InitializationRegister)
    · subst r
      rw [Function.update_self, symbolSequenceCounters_index]
      simp [cs]
    · simp [hr]
  simpa [symbolCellLoopCode, withCounter, symbolCellBody, symbolCellCost, cs, hc] using h'

theorem symbolCellBody_invariant (capacity n k : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))
    (hs : symbolCellInvariant header stackRank symbolCard tm e backward ars capacity n (k + 1) s) :
    symbolCellInvariant header stackRank symbolCard tm e backward ars capacity n k (symbolCellBody header stackRank symbolCard tm e backward ars capacity n k s) := by
  rcases hs with ⟨hk, hn, hcap, hb, ht⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · simpa [symbolCellBody, symbolSequenceCounters_metadata] using hn
  · simpa [symbolCellBody, symbolSequenceCounters_metadata] using hcap
  · simpa [symbolCellBody, symbolSequenceCounters_metadata] using hb
  · simpa [symbolCellBody, symbolSequenceCounters_metadata] using ht

/-- Full counted cell traversal with finite symbol dispatch at every cell. -/
theorem symbolCellTraversal_run (capacity n count : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))
    (hs : symbolCellInvariant header stackRank symbolCard tm e backward ars capacity n count s) :
    CounterRun (symbolCellLoopCode header stackRank symbolCard tm e backward ars) (withCounter s (.inr 0) count (symbolSequenceExit header stackRank symbolCard tm e backward ars 0))
      (descendingSteps (symbolCellBody header stackRank symbolCard tm e backward ars capacity n) (symbolCellCost header stackRank symbolCard tm e backward ars) count s)
      (withCounter (descendingResult (symbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s) (.inr 0) 0 (symbolSequenceExit header stackRank symbolCard tm e backward ars 2)) := by
  exact descending_counter_run (symbolCellLoopCode header stackRank symbolCard tm e backward ars) (.inr 0) (symbolSequenceExit header stackRank symbolCard tm e backward ars 0) (symbolSequenceExit header stackRank symbolCard tm e backward ars 1) (symbolSequenceEntry header stackRank symbolCard tm e backward ars 0) (symbolSequenceExit header stackRank symbolCard tm e backward ars 2)
    (symbolCellLoop_test header stackRank symbolCard tm e backward ars) (symbolCellLoop_pop header stackRank symbolCard tm e backward ars)
    (symbolCellBody header stackRank symbolCard tm e backward ars capacity n) (symbolCellCost header stackRank symbolCard tm e backward ars) (symbolCellInvariant header stackRank symbolCard tm e backward ars capacity n)
    (symbolCellBody_run header stackRank symbolCard tm e backward ars capacity n) (symbolCellBody_invariant header stackRank symbolCard tm e backward ars capacity n) count s hs

theorem symbolCellTraversal_output (capacity n count : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3))) :
    (descendingResult (symbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s).output =
      (List.range count).flatMap (symbolSequencePayload header stackRank symbolCard tm e backward ars capacity n) ++ s.output := by
  induction count generalizing s with
  | zero => simp [descendingResult]
  | succ k ih => rw [descendingResult, ih]; simp [symbolCellBody, List.range_succ, List.flatMap_append, List.append_assoc]

/-- The actual layer counter grows only linearly in the number of visited cells. -/
theorem symbolCellTraversal_layer_bound (capacity n count : Nat) (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3))) :
    (descendingResult (symbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s).counters (.inr 10) ≤
      s.counters (.inr 10) + count * (ars.length * 630) := by
  induction count generalizing s with
  | zero => simp [descendingResult]
  | succ k ih =>
      have h := ih (symbolCellBody header stackRank symbolCard tm e backward ars capacity n k s)
      have hb := symbolSequence_layer_bound header stackRank symbolCard tm e backward ars (Function.update s.counters (.inr 0) k)
      have hbase : (symbolCellBody header stackRank symbolCard tm e backward ars capacity n k s).counters (.inr 10) ≤
          s.counters (.inr 10) + ars.length * 630 := by
        simpa only [symbolCellBody,
          Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 0)] using hb
      simp only [descendingResult, Nat.succ_mul]
      omega

end ShiReversibleGenerator
