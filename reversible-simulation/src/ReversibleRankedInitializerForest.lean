import ReversibleRankedStackForest
import ReversibleInitializationCoordinateBlocks
import ReversibleRankedInitializerPayload

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

theorem initializationCellBlocks_stacks (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) :
    initializationCellBlocks tm e capacity n backward =
      (List.ofFn (fun k : Fin (Fintype.card tm.K) =>
        initializationRankedStackBlocks tm e capacity n ((Fintype.equivFin tm.K).symm k)
          backward)).flatten := by
  simpa only [initializationCellBlocks, initializationRankedStackBlocks,
    initializationRankedCellBlocks, List.map_ofFn, Function.comp_def] using
    (flatten_map_flatten (List.ofFn (fun k : Fin (Fintype.card tm.K) =>
      List.ofFn (fun i : Fin capacity => initializationRankedCellBlocks tm e capacity n
        ((Fintype.equivFin tm.K).symm k) i backward)))).symm

theorem rankedInitializerPayload_header_stacks (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₀ ≃ Bool) (capacity n : Nat) (backward : Bool) :
    rankedInitializerPayload tm e backward capacity n =
      if backward then
        (List.ofFn (fun k : Fin (Fintype.card tm.K) => rankedStackPayload tm e backward
          capacity n ((Fintype.equivFin tm.K).symm k))).reverse.flatten ++
          configurationHeaderPayload tm backward n
      else configurationHeaderPayload tm backward n ++
        (List.ofFn (fun k : Fin (Fintype.card tm.K) => rankedStackPayload tm e backward
          capacity n ((Fintype.equivFin tm.K).symm k))).flatten := by
  cases backward <;>
    simp [rankedInitializerPayload, rankedInitializerSchedule, initializationStackSchedule,
      List.flatMap_def, List.map_ofFn, Function.comp_def]

/-- Exact equality with the pre-existing padded initializer, rather than a new schedule description. -/
theorem rankedInitializerPayload_forest (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (backward : Bool) :
    rankedInitializerPayload tm e backward capacity n =
      ((if backward then (paddedForestCompile (fun i : Fin n => i.val) n 17
          (initialForest tm e capacity n)).reverse
        else paddedForestCompile (fun i : Fin n => i.val) n 17
          (initialForest tm e capacity n)).map (rawAssignmentPayload backward)).flatten := by
  rw [initializationForest_payload_header_cells, rankedInitializerPayload_header_stacks,
    initializationCellBlocks_stacks]
  have hstacks : (List.ofFn (fun k : Fin (Fintype.card tm.K) => rankedStackPayload tm e backward
      capacity n ((Fintype.equivFin tm.K).symm k))) =
      List.ofFn (fun k : Fin (Fintype.card tm.K) =>
        (if backward then (initializationRankedStackBlocks tm e capacity n
          ((Fintype.equivFin tm.K).symm k) backward).reverse
         else initializationRankedStackBlocks tm e capacity n
          ((Fintype.equivFin tm.K).symm k) backward).flatten) := by
    apply congrArg List.ofFn
    funext k
    exact rankedStack_forest_payload tm e capacity n ((Fintype.equivFin tm.K).symm k) backward
  rw [hstacks]
  cases backward with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    congr 1
    simpa only [List.map_ofFn, Function.comp_def] using flatten_map_flatten
      (List.ofFn (fun k : Fin (Fintype.card tm.K) =>
        initializationRankedStackBlocks tm e capacity n ((Fintype.equivFin tm.K).symm k) false))
  | true =>
    simp only [if_true]
    congr 1
    simpa only [List.map_ofFn, Function.comp_def, List.map_reverse] using flatten_reversed_blocks
      (List.ofFn (fun k : Fin (Fintype.card tm.K) =>
        initializationRankedStackBlocks tm e capacity n ((Fintype.equivFin tm.K).symm k) true))

/-- The actual finite initializer program emits exactly the established forest bytes and preserves the tail. -/
theorem rankedInitializer_output_forest (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (backward : Bool) (capacity n : Nat) (cs : InitializationRegister → Nat) (ys : List Bool)
    (hn : cs (.inl 0) = n) (hcap : cs (.inl 2) = capacity) :
    initializerSequenceOutput (rankedInitializerComponents tm e backward) n cs ys =
      ((if backward then (paddedForestCompile (fun i : Fin n => i.val) n 17
          (initialForest tm e capacity n)).reverse
        else paddedForestCompile (fun i : Fin n => i.val) n 17
          (initialForest tm e capacity n)).map (rawAssignmentPayload backward)).flatten ++ ys := by
  rw [rankedInitializer_output tm e backward capacity n cs ys hn hcap,
    rankedInitializerPayload_forest]

end ShiReversibleGenerator
