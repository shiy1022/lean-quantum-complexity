import ReversibleInitializationForestEnumeration
import ReversibleConfigurationHeaderForest

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- Actual padded cell blocks, ordered by machine rank, cell index and symbol rank. -/
noncomputable def initializationCellBlocks (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) : List (List Bool) :=
  (List.ofFn (fun k : Fin (Fintype.card tm.K) =>
    List.ofFn (fun i : Fin capacity =>
      List.ofFn (fun a : Fin (Fintype.card (Option (MachineSymbol tm))) =>
        initializationFormulaPayload
          ((initialFormulas tm e capacity n).cells ((Fintype.equivFin tm.K).symm k) i
            ((Fintype.equivFin (Option (MachineSymbol tm))).symm a)) backward
          (n + 18 * (configurationBitEquiv tm capacity
            (.inr ((((Fintype.equivFin tm.K).symm k, i),
              (Fintype.equivFin (Option (MachineSymbol tm))).symm a)))).val))))).flatten.flatten

/-- This decomposition retains the established codec's exact coordinate addresses. -/
theorem initializationForestBlocks_coordinates (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) :
    initializationForestBlocks tm e capacity n backward =
      initializationHeaderBlocks tm e capacity n backward ++
        initializationCellBlocks tm e capacity n backward := by
  classical
  have h := configurationBitEquiv_ofFn tm capacity (fun coordinate =>
    initializationFormulaPayload ((initialFormulas tm e capacity n).bitFormula
      (configurationBitEquiv tm capacity coordinate)) backward
      (n + 18 * (configurationBitEquiv tm capacity coordinate).val))
  simpa only [initializationForestBlocks, initializationHeaderBlocks,
    initializationCellBlocks, FormulaCfg.bitFormula, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply, List.append_assoc] using h

/-- Complete forest bytes split into the actual header and cells, in either direction. -/
theorem initializationForest_payload_header_cells (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₀ ≃ Bool) (capacity n : Nat) (backward : Bool) :
    ((if backward then (paddedForestCompile (fun i : Fin n => i.val) n 17
        (initialForest tm e capacity n)).reverse
      else paddedForestCompile (fun i : Fin n => i.val) n 17
        (initialForest tm e capacity n)).map (rawAssignmentPayload backward)).flatten =
      if backward then (initializationCellBlocks tm e capacity n backward).reverse.flatten ++
        configurationHeaderPayload tm backward n
      else configurationHeaderPayload tm backward n ++
        (initializationCellBlocks tm e capacity n backward).flatten := by
  rw [initializationForest_payload_blocks, initializationForestBlocks_coordinates]
  rw [configurationHeader_forest_payload tm e capacity n backward]
  cases backward <;>
    simp only [Bool.false_eq_true, if_false, if_true, List.reverse_append, List.flatten_append]

end ShiReversibleGenerator
