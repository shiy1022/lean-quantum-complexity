import ReversiblePreparedConstantExactLayers
import ReversiblePreparedInputExactLayers
import ReversibleRankedInitializerProgram
import ReversibleRangeEnumeration

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
noncomputable local instance (tm : Turing.FinTM2) : DecidableEq (MachineSymbol tm) := Classical.decEq _

noncomputable def initializationStackLayerCount (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (k : tm.K) : Nat :=
  (List.ofFn (fun i : Fin capacity =>
    (List.ofFn (fun a : Fin (Fintype.card (Option (MachineSymbol tm))) =>
      formulaElementaryLayers ((initialFormulas tm e capacity n).cells k i
        ((Fintype.equivFin (Option (MachineSymbol tm))).symm a)) + 1)).sum)).sum

theorem initializationSymbolSchedule_layerSum (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (i : Fin capacity) (backward : Bool) :
    ((initializationSymbolSchedule tm backward).map (fun ar =>
      (if i.val < n then formulaElementaryLayers (initializationInputCellSchema tm e ar.1)
       else formulaElementaryLayers (.constant (oneHot none ar.1) : Formula Unit)) + 1)).sum =
      (List.ofFn (fun a : Fin (Fintype.card (Option (MachineSymbol tm))) =>
        formulaElementaryLayers ((initialFormulas tm e capacity n).cells tm.k₀ i
          ((Fintype.equivFin (Option (MachineSymbol tm))).symm a)) + 1)).sum := by
  cases backward <;>
    simp only [initializationSymbolSchedule, Bool.false_eq_true, if_false, if_true,
      initializationSymbolRanks, List.map_reverse, List.sum_reverse, List.map_ofFn, Function.comp_def]
  all_goals
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext a
    rw [initialFormulas_input_cell_layers]

theorem initializationConstantSchedule_layerSum (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (k : tm.K) (i : Fin capacity) (hk : k ≠ tm.k₀) (backward : Bool) :
    ((initializationConstantSchedule tm backward).map (fun ar =>
      formulaElementaryLayers (.constant ar.1 : Formula Unit) + 1)).sum =
      (List.ofFn (fun a : Fin (Fintype.card (Option (MachineSymbol tm))) =>
        formulaElementaryLayers ((initialFormulas tm e capacity n).cells k i
          ((Fintype.equivFin (Option (MachineSymbol tm))).symm a)) + 1)).sum := by
  classical
  cases backward <;>
    simp only [initializationConstantSchedule, Bool.false_eq_true, if_false, if_true,
      initializationConstantRanks, List.map_reverse, List.sum_reverse, List.map_ofFn, Function.comp_def]
  all_goals
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext a
    rw [initialFormulas_padding_cell_schema tm e capacity n k i _ (Or.inl hk)]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
/-- Both prepared loop directions count exactly the established stack formulas and final copies. -/
theorem packagedInitializationStack_exact_layers (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (k : tm.K) (backward : Bool) (cs : InitializationRegister → Nat)
    (ys : List Bool) (hn : cs (.inl 0) = n) (hcap : cs (.inl 2) = capacity) :
    (packagedInitializationStack tm e backward k).counters n cs ys (.inr 10) =
      cs (.inr 10) + initializationStackLayerCount tm e capacity n k := by
  classical
  have hinput : ((List.range capacity).map (fun j =>
      ((initializationSymbolSchedule tm backward).map (fun ar =>
        (if j < n then formulaElementaryLayers (initializationInputCellSchema tm e ar.1)
         else formulaElementaryLayers (.constant (oneHot none ar.1) : Formula Unit)) + 1)).sum)).sum =
      initializationStackLayerCount tm e capacity n tm.k₀ := by
    rw [map_range_ofFn]
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext i
    exact initializationSymbolSchedule_layerSum tm e capacity n i backward
  have hconstant : k ≠ tm.k₀ → ((List.range capacity).map (fun _ =>
      ((initializationConstantSchedule tm backward).map (fun ar =>
        formulaElementaryLayers (.constant ar.1 : Formula Unit) + 1)).sum)).sum =
      initializationStackLayerCount tm e capacity n k := by
    intro hk
    rw [map_range_ofFn]
    apply congrArg List.sum
    apply congrArg List.ofFn
    funext i
    exact initializationConstantSchedule_layerSum tm e capacity n k i hk backward
  by_cases hk : k = tm.k₀
  · subst k
    cases backward <;>
      simp only [packagedInitializationStack, if_pos rfl, Bool.false_eq_true, if_false, if_true,
        packagedInputComponent, packagedAscendingInputComponent,
        preparedInputComponentResult_exact_layers, preparedAscendingInputComponentResult_exact_layers,
        hn, hcap] <;> simpa using congrArg (fun v => cs (.inr 10) + v) hinput
  · cases backward <;>
      simp only [packagedInitializationStack, if_neg hk, Bool.false_eq_true, if_false, if_true,
        packagedConstantComponent, packagedAscendingConstantComponent,
        preparedConstantComponentResult_exact_layers, preparedAscendingConstantComponentResult_exact_layers,
        hcap] <;> simpa using congrArg (fun v => cs (.inr 10) + v) (hconstant hk)

end ShiReversibleGenerator
