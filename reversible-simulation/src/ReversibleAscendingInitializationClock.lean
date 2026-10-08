import ReversibleInitializationAddressBudget
import ReversibleAscendingSymbolBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- Specialization of the actual counted loop clock to the machine's fixed symbol schedule. -/
theorem ascendingInitializationInputStack_polynomial_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (capacity initial layers : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n count
      (s : CounterCfg InitializationRegister (SymbolSequenceLabels
        (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val
        (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (Fin 4))),
      AscendingSymbolBudgetInvariant
        (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val
        (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward)
        ((initializationAddressBudget tm capacity initial).eval n) (layers.eval n) (capacity.eval n) n count s →
      descendingSteps (ascendingSymbolCellBody
        (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val
        (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward) (capacity.eval n) n)
        (ascendingSymbolCellCost (Fintype.card (Option tm.Λ) + Fintype.card tm.σ) ((Fintype.equivFin tm.K) tm.k₀).val
          (Fintype.card (Option (MachineSymbol tm))) tm e backward (initializationSymbolSchedule tm backward)) count s ≤ clock.eval n := by
  exact ascendingSymbolTraversal_polynomial_bound _ _ _ tm e backward (initializationSymbolSchedule tm backward)
    capacity (initializationAddressBudget tm capacity initial) layers
    (fun n ar h => initializationAddressBudget_addresses tm capacity initial backward n ar h)

end ShiReversibleGenerator
