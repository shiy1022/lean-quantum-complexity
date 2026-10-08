import ReversibleConstantCellTraversal
import ReversibleAscendingConstantCellTraversal

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula

theorem constantInitialization_layer_bound (value : Bool) (backward : Bool) (cs : InitializationRegister → Nat) :
    constantInitializationCounters value backward cs (.inr 10) ≤ cs (.inr 10) + 630 := by
  classical
  change fixedNodeCounters initializationNodeRegisters (constantInitializationTemplates value backward)
    (initializationAddressResult cs) initializationNodeRegisters.count ≤ _
  rw [fixedNodeCounters_count _ _ (by decide) (by decide) (by decide)]
  simp only [constantInitializationTemplates, paddedFormulaPrinter_layer_count]
  simp only [initializationNodeRegisters, initializationAddress_result]
  simp only [Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 6),
    Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 5),
    Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 4),
    Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 3),
    Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 2)]
  simp only [formulaElementaryLayers]
  split_ifs <;> omega

theorem locatedConstant_layer_bound (header stackRank symbolCard symbolRank : Nat)
    (value : Bool)
    (backward : Bool) (cs : InitializationRegister → Nat) :
    locatedConstantCounters header stackRank symbolCard symbolRank value backward cs (.inr 10) ≤
      cs (.inr 10) + 630 := by
  simpa [locatedConstantCounters, cellCoordinateResult_eq] using
    constantInitialization_layer_bound value backward
      (cellCoordinateResult header stackRank symbolCard symbolRank cs)

theorem constantSequence_layer_bound (header stackRank symbolCard : Nat)
    (backward : Bool)
    (ars : List (Bool × Nat)) (cs : InitializationRegister → Nat) :
    constantSequenceCounters header stackRank symbolCard backward ars cs (.inr 10) ≤
      cs (.inr 10) + ars.length * 630 := by
  induction ars generalizing cs with
  | nil => simp [constantSequenceCounters]
  | cons ar ars ih =>
      have h := ih (locatedConstantCounters header stackRank symbolCard ar.2 ar.1 backward cs)
      have hb := locatedConstant_layer_bound header stackRank symbolCard ar.2 ar.1 backward cs
      simp only [constantSequenceCounters, List.length_cons, Nat.succ_mul]
      omega


variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

/-- The actual layer counter grows only linearly in the number of visited cells. -/
theorem constantCellTraversal_layer_bound (capacity n count : Nat) (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 3))) :
    (descendingResult (constantCellBody header stackRank symbolCard backward ars capacity n) count s).counters (.inr 10) ≤
      s.counters (.inr 10) + count * (ars.length * 630) := by
  induction count generalizing s with
  | zero => simp [descendingResult]
  | succ k ih =>
      have h := ih (constantCellBody header stackRank symbolCard backward ars capacity n k s)
      have hb := constantSequence_layer_bound header stackRank symbolCard backward ars (Function.update s.counters (.inr 0) k)
      have hbase : (constantCellBody header stackRank symbolCard backward ars capacity n k s).counters (.inr 10) ≤
          s.counters (.inr 10) + ars.length * 630 := by
        simpa only [constantCellBody,
          Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 0)] using hb
      simp only [descendingResult, Nat.succ_mul]
      omega

/-- Incrementing the cell index leaves the independent layer count unchanged. -/
theorem ascendingConstantCellTraversal_layer_bound (capacity n count : Nat)
    (s : CounterCfg InitializationRegister (ConstantSequenceLabels header stackRank symbolCard backward ars (Fin 4))) :
    (descendingResult (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n) count s).counters (.inr 10) ≤
      s.counters (.inr 10) + count * (ars.length * 630) := by
  induction count generalizing s with
  | zero => simp [descendingResult]
  | succ k ih =>
      have h := ih (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n k s)
      have hb := constantSequence_layer_bound header stackRank symbolCard backward ars
        (Function.update s.counters (.inr 11) k)
      have hbase : (ascendingConstantCellBody header stackRank symbolCard backward ars capacity n k s).counters (.inr 10) ≤
          s.counters (.inr 10) + ars.length * 630 := by
        simpa only [ascendingConstantCellBody,
          Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 0),
          Function.update_of_ne (by decide : (Sum.inr 10 : InitializationRegister) ≠ .inr 11)] using hb
      simp only [descendingResult, Nat.succ_mul]
      omega


end ShiReversibleGenerator
