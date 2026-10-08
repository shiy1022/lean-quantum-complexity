import ReversibleTickRowPayloadEnumeration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

noncomputable def tickBoundedHeaderBlocks (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) : List (List Bool) :=
  List.ofFn (fun j : Fin (Fintype.card (Option tm.Λ)) => tickBoundedCoordinatePayload tm capacity input inputStride outputBase bound backward
    (.inl (.inl ((Fintype.equivFin (Option tm.Λ)).symm j)))) ++
  List.ofFn (fun j : Fin (Fintype.card tm.σ) => tickBoundedCoordinatePayload tm capacity input inputStride outputBase bound backward
    (.inl (.inr ((Fintype.equivFin tm.σ).symm j))))

noncomputable def tickBoundedSymbolBlocks (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) (stack : tm.K) (i : Fin capacity) : List (List Bool) :=
  List.ofFn (fun a : Fin (Fintype.card (Option (MachineSymbol tm))) =>
    tickBoundedCoordinatePayload tm capacity input inputStride outputBase bound backward
      (.inr ((stack,i),(Fintype.equivFin (Option (MachineSymbol tm))).symm a)))

/-- Symbol blocks use precisely the finite symbol ranks of the configuration codec. -/
theorem tickSymbolRowPayload_bounded (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) (stack : tm.K) (i : Fin capacity) :
    tickSymbolRowPayload tm stack inputStride bound backward input capacity outputBase i.val =
      (if backward then (tickBoundedSymbolBlocks tm capacity input inputStride outputBase bound backward stack i).reverse
       else tickBoundedSymbolBlocks tm capacity input inputStride outputBase bound backward stack i).flatten := by
  unfold tickSymbolRowPayload
  cases backward <;> simp only [Bool.false_eq_true,if_false,if_true,List.map_reverse]
  all_goals
    simp_rw [tickCoordinateSymbolicPayload_bounded tm capacity input inputStride outputBase bound _ i]
    simp [tickBoundedSymbolBlocks,tickSymbolOrder,List.map_ofFn,Function.comp_def,boundedTickCoordinate]

/-- The header's symbolic printer agrees with the bounded codec's label and memory blocks. -/
theorem tickHeaderSymbolicPayload_bounded (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) (hc : 0 < capacity) :
    tickHeaderSymbolicPayload tm inputStride bound backward input capacity outputBase =
      (if backward then (tickBoundedHeaderBlocks tm capacity input inputStride outputBase bound backward).reverse
       else tickBoundedHeaderBlocks tm capacity input inputStride outputBase bound backward).flatten := by
  let i : Fin capacity := ⟨0,hc⟩
  have h : ∀ kind, tickCoordinateSymbolicPayload tm kind inputStride bound backward input capacity outputBase 0 =
      tickBoundedCoordinatePayload tm capacity input inputStride outputBase bound backward (boundedTickCoordinate tm capacity i kind) := by
    intro kind
    exact tickCoordinateSymbolicPayload_bounded tm capacity input inputStride outputBase bound backward i kind
  unfold tickHeaderSymbolicPayload
  simp_rw [h]
  cases backward <;> simp [tickBoundedHeaderBlocks,tickHeaderKinds,List.map_ofFn,List.map_reverse,Function.comp_def,boundedTickCoordinate]

end ShiReversibleGenerator
