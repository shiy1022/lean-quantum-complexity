import ReversibleRankedStackPayload
import ReversibleConfigurationHeaderPayload

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

noncomputable def initializationRankedCellBlocks (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (k : tm.K) (i : Fin capacity) (backward : Bool) : List (List Bool) :=
  List.ofFn (fun a : Fin (Fintype.card (Option (MachineSymbol tm))) =>
    initializationFormulaPayload ((initialFormulas tm e capacity n).cells k i
      ((Fintype.equivFin (Option (MachineSymbol tm))).symm a)) backward
      (n + 18 * (configurationBitEquiv tm capacity
        (.inr ((k, i), (Fintype.equivFin (Option (MachineSymbol tm))).symm a))).val))

/-- The actual per-cell dispatch equals its formula blocks, including input padding and other stacks. -/
theorem rankedCell_forest_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (k : tm.K) (i : Fin capacity) (backward : Bool) :
    (if k = tm.k₀ then
      symbolSequencePayload (Fintype.card (Option tm.Λ) + Fintype.card tm.σ)
        ((Fintype.equivFin tm.K) k).val (Fintype.card (Option (MachineSymbol tm))) tm e backward
        (initializationSymbolSchedule tm backward) capacity n i.val
    else constantCellPayload (Fintype.card (Option tm.Λ) + Fintype.card tm.σ)
      ((Fintype.equivFin tm.K) k).val (Fintype.card (Option (MachineSymbol tm))) backward
      (initializationConstantSchedule tm backward) capacity n i.val) =
      (if backward then (initializationRankedCellBlocks tm e capacity n k i backward).reverse
       else initializationRankedCellBlocks tm e capacity n k i backward).flatten := by
  classical
  by_cases hk : k = tm.k₀
  · subst k
    simp only [if_pos rfl]
    simpa only [if_true, initializationRankedCellBlocks, initializationCellPayload,
      initializationFormulaPayload] using initializationSymbolSchedule_payload tm e capacity n i backward
  · rw [if_neg hk, constantStack_schedule_payload]
    have hblocks : ((initializationConstantRanks tm).map (fun ar =>
        constantInitializationPayload ar.1 backward
          (n + 18 * (Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
            (((Fintype.equivFin tm.K) k).val * capacity + i.val) *
              Fintype.card (Option (MachineSymbol tm)) + ar.2)))) =
        initializationRankedCellBlocks tm e capacity n k i backward := by
      rw [initializationConstantRanks, List.map_ofFn]
      apply congrArg List.ofFn
      funext a
      simpa only [Function.comp_def, Equiv.apply_symm_apply] using
        constantStack_coordinate_payload tm e capacity n k i
          ((Fintype.equivFin (Option (MachineSymbol tm))).symm a) hk backward
    cases backward <;>
      simp only [Bool.false_eq_true, if_false, if_true, List.flatMap_def, List.map_reverse, hblocks]

end ShiReversibleGenerator
