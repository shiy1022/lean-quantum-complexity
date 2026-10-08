import ReversibleRankedCellExactLayers
import ReversibleSymbolCellTraversal
import ReversibleConstantCellTraversal

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula ShiReversibleCoding
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq (MachineSymbol tm) := Classical.decEq _

theorem descendingResult_exact_measure {R L : Type} (body : Nat → CounterCfg R L → CounterCfg R L)
    (measure : CounterCfg R L → Nat) (cost : Nat → Nat) (invariant : CounterCfg R L → Prop)
    (preserved : ∀ k s, invariant s → invariant (body k s))
    (increment : ∀ k s, invariant s → measure (body k s) = measure s + cost k)
    (count : Nat) (s : CounterCfg R L) (hs : invariant s) :
    measure (descendingResult body count s) = measure s + ((List.range count).map cost).sum := by
  induction count generalizing s with
  | zero => simp [descendingResult]
  | succ k ih =>
    rw [descendingResult, ih (body k s) (preserved k s hs), increment k s hs]
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega

theorem constantCellTraversal_exact_layers (header stackRank symbolCard : Nat) (backward : Bool)
    (ars : List (Bool × Nat)) (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3))) :
    (descendingResult (constantCellBody header stackRank symbolCard backward ars capacity n) count s).counters (.inr 10) =
      s.counters (.inr 10) + ((List.range count).map (fun _ =>
        (ars.map (fun ar => formulaElementaryLayers (.constant ar.1 : Formula Unit) + 1)).sum)).sum := by
  refine descendingResult_exact_measure (constantCellBody header stackRank symbolCard backward ars capacity n)
    (fun t => t.counters (.inr 10 : InitializationRegister))
    (fun _ => (ars.map (fun ar => formulaElementaryLayers (.constant ar.1 : Formula Unit) + 1)).sum)
    (fun _ => True) ?_ ?_ count s trivial
  · intros; trivial
  · intro k s hs
    simpa [constantCellBody] using constantSequence_exact_layers header stackRank symbolCard backward ars
      (Function.update s.counters (.inr 0) k)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
theorem symbolCellTraversal_exact_layers (header stackRank symbolCard : Nat) (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))
    (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (SymbolSequenceLabels header stackRank symbolCard tm e backward ars (Fin 3)))
    (hn : s.counters (.inl 0) = n) :
    (descendingResult (symbolCellBody header stackRank symbolCard tm e backward ars capacity n) count s).counters (.inr 10) =
      s.counters (.inr 10) + ((List.range count).map (fun k =>
        (ars.map (fun ar =>
          (if k < n then formulaElementaryLayers (initializationInputCellSchema tm e ar.1)
           else formulaElementaryLayers (.constant (oneHot none ar.1) : Formula Unit)) + 1)).sum)).sum := by
  refine descendingResult_exact_measure (symbolCellBody header stackRank symbolCard tm e backward ars capacity n)
    (fun t => t.counters (.inr 10 : InitializationRegister))
    (fun k => (ars.map (fun ar =>
      (if k < n then formulaElementaryLayers (initializationInputCellSchema tm e ar.1)
       else formulaElementaryLayers (.constant (oneHot none ar.1) : Formula Unit)) + 1)).sum)
    (fun t => t.counters (.inl 0 : InitializationRegister) = n) ?_ ?_ count s hn
  · intro k s hs
    simpa [symbolCellBody, symbolSequenceCounters_metadata] using hs
  · intro k s hs
    simpa [symbolCellBody, hs] using symbolSequence_exact_layers header stackRank symbolCard tm e backward ars
      (Function.update s.counters (.inr 0) k)

end ShiReversibleGenerator
