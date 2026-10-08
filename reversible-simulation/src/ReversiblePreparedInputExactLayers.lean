import ReversibleAscendingExactLayers
import ReversiblePreparedInputComponents

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula ShiReversibleCoding
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq (MachineSymbol tm) := Classical.decEq _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
theorem preparedInputComponentResult_exact_layers (header stackRank symbolCard : Nat) (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))
    (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) (hn : cs (.inl 0) = n) :
    (preparedInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inr 10) =
      cs (.inr 10) + ((List.range (cs (.inl 2))).map (fun k =>
        (ars.map (fun ar =>
          (if k < n then formulaElementaryLayers (initializationInputCellSchema tm e ar.1)
           else formulaElementaryLayers (.constant (oneHot none ar.1) : Formula Unit)) + 1)).sum)).sum := by
  let reset := cleanupCounters initializationLoopReset cs
  have hn' : (inputComponentStartCfg header stackRank symbolCard tm e backward ars reset ys).counters (.inl 0) = n := by
    simpa [inputComponentStartCfg, constantComponentStart, reset, initializationLoopReset_counters] using hn
  have h := symbolCellTraversal_exact_layers header stackRank symbolCard tm e backward ars (reset (.inl 2)) n
    (reset (.inl 2)) (inputComponentStartCfg header stackRank symbolCard tm e backward ars reset ys) hn'
  simpa [preparedInputComponentResult, CounterCfg.relabel, inputComponentResult, withCounter,
    inputComponentStartCfg, constantComponentStart, reset, initializationLoopReset_counters] using h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
theorem preparedAscendingInputComponentResult_exact_layers (header stackRank symbolCard : Nat) (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))
    (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) (hn : cs (.inl 0) = n) :
    (preparedAscendingInputComponentResult header stackRank symbolCard tm e backward ars n cs ys).counters (.inr 10) =
      cs (.inr 10) + ((List.range (cs (.inl 2))).map (fun k =>
        (ars.map (fun ar =>
          (if k < n then formulaElementaryLayers (initializationInputCellSchema tm e ar.1)
           else formulaElementaryLayers (.constant (oneHot none ar.1) : Formula Unit)) + 1)).sum)).sum := by
  let reset := cleanupCounters initializationLoopReset cs
  have hn' : (ascendingInputComponentStartCfg header stackRank symbolCard tm e backward ars reset ys).counters (.inl 0) = n := by
    simpa [ascendingInputComponentStartCfg, ascendingConstantComponentStart, reset, initializationLoopReset_counters] using hn
  have h := ascendingSymbolCellTraversal_exact_layers header stackRank symbolCard tm e backward ars (reset (.inl 2)) n
    (reset (.inl 2)) (ascendingInputComponentStartCfg header stackRank symbolCard tm e backward ars reset ys) hn'
  simpa [preparedAscendingInputComponentResult, CounterCfg.relabel, ascendingInputComponentResult, withCounter,
    ascendingInputComponentStartCfg, ascendingConstantComponentStart, reset, initializationLoopReset_counters] using h

end ShiReversibleGenerator
