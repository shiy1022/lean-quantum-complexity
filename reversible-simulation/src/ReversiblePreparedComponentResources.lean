import ReversibleInitializerSequenceClock
import ReversibleInitializerComponentPackages

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM

section
variable (header stackRank symbolCard : Nat) (backward : Bool) (ars : List (Bool × Nat))

set_option backward.isDefEq.respectTransparency false in
noncomputable def packagedConstantComponent_resources (capacity budget : Polynomial Nat)
    (haddr : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    InitializationResources (packagedConstantComponent header stackRank symbolCard backward ars) capacity budget := by
  refine {
    growth := ars.length * 630
    layers := preparedConstantComponentResult_layer_bound header stackRank symbolCard backward ars
    preserved := ?_
    clock := fun layers => preparedConstantComponent_polynomial_bound header stackRank symbolCard backward ars capacity budget layers haddr }
  intro n cs ys hn hcap hb ht hbudget
  exact preparedConstantComponentResult_budget header stackRank symbolCard backward ars n (budget.eval n) (cs (.inr 10)) cs hn hb ht hbudget
    (Nat.le_refl _) (by simpa only [hcap] using haddr n) ys

set_option backward.isDefEq.respectTransparency false in
noncomputable def packagedAscendingConstantComponent_resources (capacity budget : Polynomial Nat)
    (haddr : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    InitializationResources (packagedAscendingConstantComponent header stackRank symbolCard backward ars) capacity budget := by
  refine {
    growth := ars.length * 630
    layers := preparedAscendingConstantComponentResult_layer_bound header stackRank symbolCard backward ars
    preserved := ?_
    clock := fun layers => preparedAscendingConstantComponent_polynomial_bound header stackRank symbolCard backward ars capacity budget layers haddr }
  intro n cs ys hn hcap hb ht hbudget
  exact preparedAscendingConstantComponentResult_budget header stackRank symbolCard backward ars n (budget.eval n) (cs (.inr 10)) cs hn hb ht hbudget
    (Nat.le_refl _) (by simpa only [hcap] using haddr n) ys

end

section
variable (header stackRank symbolCard : Nat) (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) (backward : Bool) (ars : List (Option (MachineSymbol tm) × Nat))

set_option backward.isDefEq.respectTransparency false in
noncomputable def packagedInputComponent_resources (capacity budget : Polynomial Nat)
    (haddr : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    InitializationResources (packagedInputComponent header stackRank symbolCard tm e backward ars) capacity budget := by
  refine {
    growth := ars.length * 630
    layers := preparedInputComponentResult_layer_bound header stackRank symbolCard tm e backward ars
    preserved := ?_
    clock := fun layers => preparedInputComponent_polynomial_bound header stackRank symbolCard tm e backward ars capacity budget layers haddr }
  intro n cs ys hn hcap hb ht hbudget
  exact preparedInputComponentResult_budget header stackRank symbolCard tm e backward ars n (budget.eval n) (cs (.inr 10)) cs hn hb ht hbudget
    (Nat.le_refl _) (by simpa only [hcap] using haddr n) ys

set_option backward.isDefEq.respectTransparency false in
noncomputable def packagedAscendingInputComponent_resources (capacity budget : Polynomial Nat)
    (haddr : ∀ n ar, ar ∈ ars → n +
      18 * (header + (stackRank * capacity.eval n + capacity.eval n) * symbolCard + ar.2) + 18 ≤ budget.eval n) :
    InitializationResources (packagedAscendingInputComponent header stackRank symbolCard tm e backward ars) capacity budget := by
  refine {
    growth := ars.length * 630
    layers := preparedAscendingInputComponentResult_layer_bound header stackRank symbolCard tm e backward ars
    preserved := ?_
    clock := fun layers => preparedAscendingInputComponent_polynomial_bound header stackRank symbolCard tm e backward ars capacity budget layers haddr }
  intro n cs ys hn hcap hb ht hbudget
  exact preparedAscendingInputComponentResult_budget header stackRank symbolCard tm e backward ars n (budget.eval n) (cs (.inr 10)) cs hn hb ht hbudget
    (Nat.le_refl _) (by simpa only [hcap] using haddr n) ys

end

end ShiReversibleGenerator
