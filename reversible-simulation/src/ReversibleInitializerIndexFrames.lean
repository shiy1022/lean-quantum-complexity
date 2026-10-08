import ReversibleMachineInitializationBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM

section
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

set_option backward.isDefEq.respectTransparency false in
theorem packagedConstantComponent_index (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (packagedConstantComponent header stackRank symbolCard backward ars).counters n cs ys (.inr 0) = 0 := by
  exact constantComponentResult_zero header stackRank symbolCard backward ars n (cleanupCounters initializationLoopReset cs) ys

set_option backward.isDefEq.respectTransparency false in
theorem packagedAscendingConstantComponent_index (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (packagedAscendingConstantComponent header stackRank symbolCard backward ars).counters n cs ys (.inr 0) = cs (.inl 2) := by
  simp [packagedAscendingConstantComponent, preparedAscendingConstantComponentResult, ascendingConstantComponentResult, withCounter,
    ascendingConstantCellTraversal_index, ascendingConstantComponentStartCfg, ascendingConstantComponentStart,
    initializationLoopReset_metadata, initializationLoopReset_index]

end

section
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

set_option backward.isDefEq.respectTransparency false in
theorem packagedInputComponent_index (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (packagedInputComponent header stackRank symbolCard tm e backward ars).counters n cs ys (.inr 0) = 0 := by
  exact inputComponentResult_zero header stackRank symbolCard tm e backward ars n (cleanupCounters initializationLoopReset cs) ys

set_option backward.isDefEq.respectTransparency false in
theorem packagedAscendingInputComponent_index (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (packagedAscendingInputComponent header stackRank symbolCard tm e backward ars).counters n cs ys (.inr 0) = cs (.inl 2) := by
  simp [packagedAscendingInputComponent, preparedAscendingInputComponentResult, ascendingInputComponentResult, withCounter,
    ascendingSymbolCellTraversal_index, ascendingInputComponentStartCfg, ascendingConstantComponentStart,
    initializationLoopReset_metadata, initializationLoopReset_index]

end

local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

set_option backward.isDefEq.respectTransparency false in
theorem packagedInitializationStack_index_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (capacity n : Nat) (k : tm.K) (cs : InitializationRegister → Nat)
    (ys : List Bool) (hcap : cs (.inl 2) = capacity) :
    (packagedInitializationStack tm e backward k).counters n cs ys (.inr 0) ≤ capacity := by
  classical
  cases backward <;> by_cases hk : k = tm.k₀ <;>
    simp [packagedInitializationStack, hk, packagedConstantComponent_index,
      packagedAscendingConstantComponent_index, packagedInputComponent_index, packagedAscendingInputComponent_index, hcap]

end ShiReversibleGenerator
