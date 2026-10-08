import ReversibleAscendingExactLayers
import ReversiblePreparedConstantComponents

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula

set_option backward.isDefEq.respectTransparency false in
theorem preparedConstantComponentResult_exact_layers (header stackRank symbolCard : Nat) (backward : Bool)
    (ars : List (Bool × Nat)) (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inr 10) =
      cs (.inr 10) + ((List.range (cs (.inl 2))).map (fun _ =>
        (ars.map (fun ar => formulaElementaryLayers (.constant ar.1 : Formula Unit) + 1)).sum)).sum := by
  let reset := cleanupCounters initializationLoopReset cs
  have h := constantCellTraversal_exact_layers header stackRank symbolCard backward ars (reset (.inl 2)) n
    (reset (.inl 2)) (constantComponentStartCfg header stackRank symbolCard backward ars reset ys)
  simpa [preparedConstantComponentResult, CounterCfg.relabel, constantComponentResult, withCounter,
    constantComponentStartCfg, constantComponentStart, reset, initializationLoopReset_counters] using h

set_option backward.isDefEq.respectTransparency false in
theorem preparedAscendingConstantComponentResult_exact_layers (header stackRank symbolCard : Nat) (backward : Bool)
    (ars : List (Bool × Nat)) (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (preparedAscendingConstantComponentResult header stackRank symbolCard backward ars n cs ys).counters (.inr 10) =
      cs (.inr 10) + ((List.range (cs (.inl 2))).map (fun _ =>
        (ars.map (fun ar => formulaElementaryLayers (.constant ar.1 : Formula Unit) + 1)).sum)).sum := by
  let reset := cleanupCounters initializationLoopReset cs
  have h := ascendingConstantCellTraversal_exact_layers header stackRank symbolCard backward ars (reset (.inl 2)) n
    (reset (.inl 2)) (ascendingConstantComponentStartCfg header stackRank symbolCard backward ars reset ys)
  simpa [preparedAscendingConstantComponentResult, CounterCfg.relabel, ascendingConstantComponentResult, withCounter,
    ascendingConstantComponentStartCfg, ascendingConstantComponentStart, reset, initializationLoopReset_counters] using h

end ShiReversibleGenerator
