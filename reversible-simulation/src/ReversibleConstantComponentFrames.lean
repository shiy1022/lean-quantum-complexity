import ReversibleConstantComponent
import ReversibleAscendingConstantComponent

set_option autoImplicit false
namespace ShiReversibleGenerator
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

theorem constantComponentResult_metadata (n : Nat) (cs : InitializationRegister → Nat)
    (ys : List Bool) (r : WorkspaceRegister) :
    (constantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inl r) = cs (.inl r) := by
  simp [constantComponentResult, withCounter, constantCellTraversal_metadata, constantComponentStartCfg, constantComponentStart]

theorem constantComponentResult_zero (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (constantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inr 0) = 0 := by
  simp [constantComponentResult, withCounter]

theorem constantComponentResult_output (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (constantComponentResult header stackRank symbolCard backward ars n cs ys).output =
    (List.range (cs (.inl 2))).flatMap (constantCellPayload header stackRank symbolCard backward ars (cs (.inl 2)) n) ++ ys := by
  simp [constantComponentResult, withCounter, constantCellTraversal_output, constantComponentStartCfg, constantComponentStart]

theorem ascendingConstantComponentResult_metadata (n : Nat) (cs : InitializationRegister → Nat)
    (ys : List Bool) (r : WorkspaceRegister) :
    (ascendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inl r) = cs (.inl r) := by
  simp [ascendingConstantComponentResult, withCounter, ascendingConstantCellTraversal_metadata, ascendingConstantComponentStartCfg, ascendingConstantComponentStart]

theorem ascendingConstantComponentResult_zero (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (ascendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inr 11) = 0 := by
  simp [ascendingConstantComponentResult, withCounter]

theorem ascendingConstantComponentResult_output (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (ascendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).output =
    ascendingConstantCellPayload header stackRank symbolCard backward ars (cs (.inl 2)) n (cs (.inl 2)) (cs (.inr 0)) ++ ys := by
  simp [ascendingConstantComponentResult, withCounter, ascendingConstantCellTraversal_output, ascendingConstantComponentStartCfg, ascendingConstantComponentStart]

end ShiReversibleGenerator
