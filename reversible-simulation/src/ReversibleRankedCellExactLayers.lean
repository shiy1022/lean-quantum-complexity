import ReversibleInitializationSequenceExactLayers
import ReversibleRankedInitializerProgram

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

theorem configurationHeader_exact_layers (tm : Turing.FinTM2) (backward : Bool)
    (cs : InitializationRegister → Nat) :
    constantSequenceCounters 0 0 0 backward (initializationHeaderSchedule tm backward) cs (.inr 10) =
      cs (.inr 10) + ((initializationHeaderRanks tm).map (fun ar =>
        formulaElementaryLayers (.constant ar.1 : Formula Unit) + 1)).sum := by
  rw [constantSequence_exact_layers]
  cases backward <;> simp [initializationHeaderSchedule, List.map_reverse]

theorem symbolSchedule_formula_layers (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (i : Fin capacity) (backward : Bool) (cs : InitializationRegister → Nat)
    (hn : cs (.inl 0) = n) (hi : cs (.inr 0) = i.val) :
    symbolSequenceCounters (Fintype.card (Option tm.Λ) + Fintype.card tm.σ)
      ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm)))
      tm e backward (initializationSymbolSchedule tm backward) cs (.inr 10) =
      cs (.inr 10) + (List.ofFn (fun a : Fin (Fintype.card (Option (MachineSymbol tm))) =>
        formulaElementaryLayers ((initialFormulas tm e capacity n).cells tm.k₀ i
          ((Fintype.equivFin (Option (MachineSymbol tm))).symm a)) + 1)).sum := by
  classical
  rw [symbolSequence_exact_layers]
  cases backward <;>
    simp only [initializationSymbolSchedule, Bool.false_eq_true, if_false, if_true,
      initializationSymbolRanks, List.map_reverse, List.sum_reverse, List.map_ofFn,
      Function.comp_def, hn, hi]
  all_goals
    apply congrArg (fun v => cs (.inr 10) + v)
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext a
    rw [initialFormulas_input_cell_layers]

theorem constantSchedule_formula_layers (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (k : tm.K) (i : Fin capacity) (hk : k ≠ tm.k₀)
    (backward : Bool) (cs : InitializationRegister → Nat) :
    constantSequenceCounters (Fintype.card (Option tm.Λ) + Fintype.card tm.σ)
      ((Fintype.equivFin tm.K) k).val (Fintype.card (Option (MachineSymbol tm)))
      backward (initializationConstantSchedule tm backward) cs (.inr 10) =
      cs (.inr 10) + (List.ofFn (fun a : Fin (Fintype.card (Option (MachineSymbol tm))) =>
        formulaElementaryLayers ((initialFormulas tm e capacity n).cells k i
          ((Fintype.equivFin (Option (MachineSymbol tm))).symm a)) + 1)).sum := by
  classical
  rw [constantSequence_exact_layers]
  cases backward <;>
    simp only [initializationConstantSchedule, Bool.false_eq_true, if_false, if_true,
      initializationConstantRanks, List.map_reverse, List.sum_reverse, List.map_ofFn,
      Function.comp_def]
  all_goals
    apply congrArg (fun v => cs (.inr 10) + v)
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext a
    rw [initialFormulas_padding_cell_schema tm e capacity n k i _ (Or.inl hk)]
    rfl

end ShiReversibleGenerator
