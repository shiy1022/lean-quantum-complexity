import ReversibleDescendingExactLayers
import ReversibleAscendingSymbolCellTraversal
import ReversibleAscendingConstantCellTraversal

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula ShiReversibleCoding
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq (MachineSymbol tm) := Classical.decEq _

/-- The descending remaining-count loop can accumulate a cost at an ascending position. -/
theorem ascendingResult_exact_measure {R L : Type} (body : Nat → CounterCfg R L → CounterCfg R L)
    (measure position : CounterCfg R L → Nat) (cost : Nat → Nat) (invariant : CounterCfg R L → Prop)
    (preserved : ∀ k s, invariant s → invariant (body k s))
    (advanced : ∀ k s, invariant s → position (body k s) = position s + 1)
    (increment : ∀ k s, invariant s → measure (body k s) = measure s + cost (position s))
    (count : Nat) (s : CounterCfg R L) (hs : invariant s) :
    measure (descendingResult body count s) = measure s +
      ((List.range count).map (fun j => cost (position s + j))).sum := by
  induction count generalizing s with
  | zero => simp [descendingResult]
  | succ k ih =>
    rw [descendingResult, ih (body k s) (preserved k s hs), increment k s hs,
      advanced k s hs]
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
      List.sum_cons, Nat.add_zero]
    have hmap : (List.range k).map (fun j => cost (position s + 1 + j)) =
        (List.range k).map (fun j => cost (position s + (j + 1))) := by
      apply List.map_congr_left
      intro j hj
      congr 1
      omega
    rw [hmap]
    simp only [Nat.succ_eq_add_one]
    omega

theorem ascendingConstantCellTraversal_exact_layers (header stackRank symbolCard : Nat) (backward : Bool)
    (ars : List (Bool × Nat)) (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4))) :
    (descendingResult (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n) count s).counters (.inr 10) =
      s.counters (.inr 10) + ((List.range count).map (fun _ =>
        (ars.map (fun ar => formulaElementaryLayers (.constant ar.1 : Formula Unit) + 1)).sum)).sum := by
  refine descendingResult_exact_measure (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n)
    (fun t => t.counters (.inr 10 : InitializationRegister))
    (fun _ => (ars.map (fun ar => formulaElementaryLayers (.constant ar.1 : Formula Unit) + 1)).sum)
    (fun _ => True) ?_ ?_ count s trivial
  · intros; trivial
  · intro k s hs
    simpa [ascendingConstantCellBody] using constantSequence_exact_layers header stackRank symbolCard backward ars
      (Function.update s.counters (.inr 11) k)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
theorem ascendingSymbolCellTraversal_exact_layers (header stackRank symbolCard : Nat) (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))
    (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 4)))
    (hn : s.counters (.inl 0) = n) :
    (descendingResult (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s).counters (.inr 10) =
      s.counters (.inr 10) + ((List.range count).map (fun j =>
        (ars.map (fun ar =>
          (if s.counters (.inr 0) + j < n then formulaElementaryLayers (initializationInputCellSchema tm e ar.1)
           else formulaElementaryLayers (.constant (oneHot none ar.1) : Formula Unit)) + 1)).sum)).sum := by
  refine ascendingResult_exact_measure (ascendingSymbolCellBody header stackRank symbolCard tm e backward ars capacity n)
    (fun t => t.counters (.inr 10 : InitializationRegister))
    (fun t => t.counters (.inr 0 : InitializationRegister))
    (fun j => (ars.map (fun ar =>
      (if j < n then formulaElementaryLayers (initializationInputCellSchema tm e ar.1)
       else formulaElementaryLayers (.constant (oneHot none ar.1) : Formula Unit)) + 1)).sum)
    (fun t => t.counters (.inl 0 : InitializationRegister) = n) ?_ ?_ ?_ count s hn
  · intro k s hs
    simpa [ascendingSymbolCellBody, symbolSequenceCounters_metadata] using hs
  · intro k s hs
    simp [ascendingSymbolCellBody]
  · intro k s hs
    simpa [ascendingSymbolCellBody, hs] using symbolSequence_exact_layers header stackRank symbolCard tm e backward ars
      (Function.update s.counters (.inr 11) k)

end ShiReversibleGenerator
