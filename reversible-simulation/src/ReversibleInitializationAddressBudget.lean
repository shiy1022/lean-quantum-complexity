import ReversibleInitializationSymbolOrder
import ReversibleSymbolTraversalBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

theorem initializationSymbolSchedule_rank_bound (tm : Turing.FinTM2) (backward : Bool)
    (ar : Option (MachineSymbol tm) × Nat) (h : ar ∈ initializationSymbolSchedule tm backward) :
    ar.2 < Fintype.card (Option (MachineSymbol tm)) := by
  have hr : ar ∈ initializationSymbolRanks tm := by
    cases backward <;> simpa [initializationSymbolSchedule] using h
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact i.isLt

noncomputable def initializationAddressBudget (tm : Turing.FinTM2) (capacity initial : Polynomial Nat) : Polynomial Nat :=
  initial + capacity + Polynomial.X + Polynomial.C 18 *
    (Polynomial.C (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) +
      Polynomial.C (((Fintype.equivFin tm.K) tm.k₀).val + 1) * capacity *
        Polynomial.C (Fintype.card (Option (MachineSymbol tm))) +
      Polynomial.C (Fintype.card (Option (MachineSymbol tm)))) + Polynomial.C 18

theorem initializationAddressBudget_initial (tm : Turing.FinTM2) (capacity initial : Polynomial Nat) (n : Nat) :
    initial.eval n ≤ (initializationAddressBudget tm capacity initial).eval n := by
  simp only [initializationAddressBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

theorem initializationAddressBudget_capacity (tm : Turing.FinTM2) (capacity initial : Polynomial Nat) (n : Nat) :
    capacity.eval n ≤ (initializationAddressBudget tm capacity initial).eval n := by
  simp only [initializationAddressBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

/-- The machine ranks give a fixed polynomial budget covering every visited cell address. -/
theorem initializationAddressBudget_addresses (tm : Turing.FinTM2) (capacity initial : Polynomial Nat)
    (backward : Bool) (n : Nat) (ar : Option (MachineSymbol tm) × Nat)
    (h : ar ∈ initializationSymbolSchedule tm backward) :
    n + 18 * (Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
      (((Fintype.equivFin tm.K) tm.k₀).val * capacity.eval n + capacity.eval n) *
        Fintype.card (Option (MachineSymbol tm)) + ar.2) + 18 ≤
      (initializationAddressBudget tm capacity initial).eval n := by
  have hr := initializationSymbolSchedule_rank_bound tm backward ar h
  have he : ((Fintype.equivFin tm.K) tm.k₀).val * capacity.eval n + capacity.eval n =
      (((Fintype.equivFin tm.K) tm.k₀).val + 1) * capacity.eval n := by ring
  rw [he]
  simp only [initializationAddressBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  omega

/-- Specialization of the actual counted loop clock to the machine's fixed symbol schedule. -/
theorem initializationInputStack_polynomial_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (capacity initial layers : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n count
      (s : CounterCfg InitializationRegister (SymbolSequenceLabels
        (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val
        (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (Fin 3))),
      SymbolCellBudgetInvariant
        (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val
        (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward)
        ((initializationAddressBudget tm capacity initial).eval n) (layers.eval n) (capacity.eval n) n count s →
      descendingSteps (symbolCellBody
        (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val
        (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (capacity.eval n) n)
        (symbolCellCost (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val
          (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward)) count s ≤ clock.eval n := by
  exact symbolCellTraversal_polynomial_bound _ _ _ tm e backward (initializationSymbolSchedule tm backward)
    capacity (initializationAddressBudget tm capacity initial) layers
    (fun n ar h => initializationAddressBudget_addresses tm capacity initial backward n ar h)

end ShiReversibleGenerator
