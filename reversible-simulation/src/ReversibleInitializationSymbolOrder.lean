import ReversibleInitializationSymbolSequence

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleCoding
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

/-- Fixed machine symbol ranks; this list never depends on input length or capacity. -/
noncomputable def initializationSymbolRanks (tm : Turing.FinTM2) : List (Option (MachineSymbol tm) × Nat) :=
  List.ofFn (fun j : Fin (Fintype.card (Option (MachineSymbol tm))) =>
    ((Fintype.equivFin (Option (MachineSymbol tm))).symm j, j.val))

noncomputable def initializationSymbolSchedule (tm : Turing.FinTM2) (backward : Bool) :=
  if backward then initializationSymbolRanks tm else (initializationSymbolRanks tm).reverse

/-- The payload of one fixed ranked symbol agrees with its established configuration coordinate. -/
theorem initializationRankedSymbol_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (i : Fin capacity) (backward : Bool)
    (j : Fin (Fintype.card (Option (MachineSymbol tm)))) :
    locatedCellPayload (Fintype.card (Option tm.Λ) + Fintype.card tm.σ)
      ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) j.val
      tm e ((Fintype.equivFin (Option (MachineSymbol tm))).symm j) backward capacity n i.val =
    initializationCellPayload tm e capacity n i ((Fintype.equivFin (Option (MachineSymbol tm))).symm j) backward
      (n + 18 * (configurationBitEquiv tm capacity
        (.inr ((tm.k₀, i), (Fintype.equivFin (Option (MachineSymbol tm))).symm j))).val) := by
  classical
  simp only [locatedCellPayload, dif_pos i.isLt, configurationBitEquiv_cell_val, Equiv.apply_symm_apply]

/-- Prepending forces the fixed symbol schedule to reverse between compute and uncompute. -/
theorem initializationSymbolSchedule_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) (i : Fin capacity) (backward : Bool) :
    symbolSequencePayload (Fintype.card (Option tm.Λ) + Fintype.card tm.σ)
      ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) tm e backward
      (initializationSymbolSchedule tm backward) capacity n i.val =
    let payloads := List.ofFn (fun j : Fin (Fintype.card (Option (MachineSymbol tm))) =>
      initializationCellPayload tm e capacity n i ((Fintype.equivFin (Option (MachineSymbol tm))).symm j) backward
        (n + 18 * (configurationBitEquiv tm capacity
          (.inr ((tm.k₀, i), (Fintype.equivFin (Option (MachineSymbol tm))).symm j))).val))
    (if backward then payloads.reverse else payloads).flatten := by
  classical
  have h : (initializationSymbolRanks tm).map (fun ar =>
      locatedCellPayload (Fintype.card (Option tm.Λ) + Fintype.card tm.σ)
        ((Fintype.equivFin tm.K) tm.k₀).val (Fintype.card (Option (MachineSymbol tm))) ar.2
        tm e ar.1 backward capacity n i.val) =
      (List.ofFn (fun j : Fin (Fintype.card (Option (MachineSymbol tm))) =>
        initializationCellPayload tm e capacity n i ((Fintype.equivFin (Option (MachineSymbol tm))).symm j) backward
          (n + 18 * (configurationBitEquiv tm capacity
            (.inr ((tm.k₀, i), (Fintype.equivFin (Option (MachineSymbol tm))).symm j))).val))) := by
    rw [initializationSymbolRanks, List.map_ofFn]
    congr 1
    funext j
    exact initializationRankedSymbol_payload tm e capacity n i backward j
  cases backward with
  | false =>
      simp only [symbolSequencePayload, initializationSymbolSchedule, Bool.false_eq_true, if_false,
        List.reverse_reverse, List.flatMap]
      rw [h]
  | true =>
      simp only [symbolSequencePayload, initializationSymbolSchedule, if_true, List.flatMap, List.map_reverse]
      rw [h]

end ShiReversibleGenerator
