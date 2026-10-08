import ReversibleRankedCellForest
import ReversibleRangeEnumeration

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
variable {α : Type}

theorem flatten_map_flatten (blocks : List (List (List α))) :
    (blocks.map List.flatten).flatten = blocks.flatten.flatten := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.flatten_append, ih]

theorem flatten_reversed_blocks (blocks : List (List (List α))) :
    (blocks.reverse.map (fun block => block.reverse.flatten)).flatten =
      blocks.flatten.reverse.flatten := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.reverse_append, ih]

noncomputable def initializationRankedStackBlocks (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (k : tm.K) (backward : Bool) : List (List Bool) :=
  (List.ofFn (fun i : Fin capacity =>
    initializationRankedCellBlocks tm e capacity n k i backward)).flatten

/-- Both actual cell-loop directions print exactly the established stack-coordinate blocks. -/
theorem rankedStack_forest_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (k : tm.K) (backward : Bool) :
    rankedStackPayload tm e backward capacity n k =
      (if backward then (initializationRankedStackBlocks tm e capacity n k backward).reverse
       else initializationRankedStackBlocks tm e capacity n k backward).flatten := by
  classical
  let cells := fun index => if k = tm.k₀ then
    symbolSequencePayload (Fintype.card (Option tm.Λ) + Fintype.card tm.σ)
      ((Fintype.equivFin tm.K) k).val
      (Fintype.card (Option (MachineSymbol tm))) tm e backward
      (initializationSymbolSchedule tm backward) capacity n index
    else constantCellPayload (Fintype.card (Option tm.Λ) + Fintype.card tm.σ)
      ((Fintype.equivFin tm.K) k).val
      (Fintype.card (Option (MachineSymbol tm))) backward
      (initializationConstantSchedule tm backward) capacity n index
  have hcells : (List.range capacity).map cells =
      List.ofFn (fun i : Fin capacity =>
        (if backward then (initializationRankedCellBlocks tm e capacity n k i backward).reverse
         else initializationRankedCellBlocks tm e capacity n k i backward).flatten) := by
    rw [map_range_ofFn]
    apply congrArg List.ofFn
    funext i
    exact rankedCell_forest_payload tm e capacity n k i backward
  change (if backward then (List.range capacity).reverse else List.range capacity).flatMap cells = _
  cases backward with
  | false =>
    simp only [Bool.false_eq_true, if_false, List.flatMap_def, hcells,
      initializationRankedStackBlocks]
    simpa only [List.map_ofFn, Function.comp_def] using flatten_map_flatten
      (List.ofFn (fun i : Fin capacity => initializationRankedCellBlocks tm e capacity n k i false))
  | true =>
    simp only [if_true, List.flatMap_def, List.map_reverse, hcells,
      initializationRankedStackBlocks]
    simpa only [List.map_ofFn, Function.comp_def, List.map_reverse] using flatten_reversed_blocks
      (List.ofFn (fun i : Fin capacity => initializationRankedCellBlocks tm e capacity n k i true))

end ShiReversibleGenerator
