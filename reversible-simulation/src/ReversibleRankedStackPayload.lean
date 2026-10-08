import ReversibleRankedInitializerProgram
import ReversibleAscendingSymbolOrder
import ReversibleAscendingConstantOrder

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

section
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

set_option backward.isDefEq.respectTransparency false in
theorem packagedConstantComponent_output (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (packagedConstantComponent header stackRank symbolCard backward ars).output n cs ys = (List.range (cs (.inl 2))).flatMap (constantCellPayload header stackRank symbolCard backward ars (cs (.inl 2)) n) ++ ys := by
  exact preparedConstantComponentResult_output header stackRank symbolCard backward ars n cs ys

set_option backward.isDefEq.respectTransparency false in
theorem packagedAscendingConstantComponent_output (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (packagedAscendingConstantComponent header stackRank symbolCard backward ars).output n cs ys = ascendingConstantCellPayload header stackRank symbolCard backward ars (cs (.inl 2)) n (cs (.inl 2)) 0 ++ ys := by
  exact preparedAscendingConstantComponentResult_output header stackRank symbolCard backward ars n cs ys

end

section
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

set_option backward.isDefEq.respectTransparency false in
theorem packagedInputComponent_output (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (packagedInputComponent header stackRank symbolCard tm e backward ars).output n cs ys = (List.range (cs (.inl 2))).flatMap (symbolSequencePayload header stackRank symbolCard tm e backward ars (cs (.inl 2)) n) ++ ys := by
  exact preparedInputComponentResult_output header stackRank symbolCard tm e backward ars n cs ys

set_option backward.isDefEq.respectTransparency false in
theorem packagedAscendingInputComponent_output (n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool) :
    (packagedAscendingInputComponent header stackRank symbolCard tm e backward ars).output n cs ys = ascendingSymbolCellPayload header stackRank symbolCard tm e backward ars (cs (.inl 2)) n (cs (.inl 2)) 0 ++ ys := by
  exact preparedAscendingInputComponentResult_output header stackRank symbolCard tm e backward ars n cs ys

end

noncomputable def rankedStackPayload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (capacity n : Nat) (k : tm.K) : List Bool := by
  classical
  let header := Fintype.card (Option tm.Λ) + Fintype.card tm.σ
  let rank := ((Fintype.equivFin tm.K) k).val
  let card := Fintype.card (Option (MachineSymbol tm))
  let indices := if backward then (List.range capacity).reverse else List.range capacity
  exact indices.flatMap (fun index => if k = tm.k₀ then
    symbolSequencePayload header rank card tm e backward (initializationSymbolSchedule tm backward) capacity n index
    else constantCellPayload header rank card backward (initializationConstantSchedule tm backward) capacity n index)

set_option backward.isDefEq.respectTransparency false in
/-- Runtime loop cleanup removes all dependence on an earlier component's private cell index. -/
theorem packagedInitializationStack_output (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (capacity n : Nat) (k : tm.K) (cs : InitializationRegister → Nat)
    (ys : List Bool) (hcap : cs (.inl 2) = capacity) :
    (packagedInitializationStack tm e backward k).output n cs ys = rankedStackPayload tm e backward capacity n k ++ ys := by
  classical
  cases backward <;> by_cases hk : k = tm.k₀ <;>
    simp [packagedInitializationStack, rankedStackPayload, hk,
      packagedInputComponent_output, packagedAscendingInputComponent_output,
      packagedConstantComponent_output, packagedAscendingConstantComponent_output,
      ascendingSymbolCellPayload_reverse_range, ascendingConstantCellPayload_reverse_range, hcap]

set_option backward.isDefEq.respectTransparency false in
theorem packagedConfigurationHeader_output (tm : Turing.FinTM2) (backward : Bool) (n : Nat)
    (cs : InitializationRegister → Nat) (ys : List Bool) (hn : cs (.inl 0) = n) :
    (packagedConfigurationHeader tm backward).output n cs ys = configurationHeaderPayload tm backward n ++ ys := by
  simp only [packagedConfigurationHeader, hn]

end ShiReversibleGenerator
