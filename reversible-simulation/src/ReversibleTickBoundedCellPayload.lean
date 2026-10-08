import ReversibleTickBoundedPayloadBlocks

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin

noncomputable def tickBoundedStackBlocks (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) (stack : tm.K) : List (List Bool) :=
  (List.ofFn (fun i : Fin capacity => tickBoundedSymbolBlocks tm capacity input inputStride outputBase bound backward stack i)).flatten

noncomputable def tickBoundedCellBlocks (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) : List (List Bool) :=
  (List.ofFn (fun k : Fin (Fintype.card tm.K) => tickBoundedStackBlocks tm capacity input inputStride outputBase bound backward
    ((Fintype.equivFin tm.K).symm k))).flatten

theorem tickSymbolRowDescendingBytes_bounded (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (stack : tm.K) :
    tickSymbolRowDescendingBytes tm stack inputStride bound false input capacity outputBase capacity =
      (tickBoundedStackBlocks tm capacity input inputStride outputBase bound false stack).flatten := by
  rw [tickSymbolRowDescendingBytes_ofFn]
  simp_rw [tickSymbolRowPayload_bounded]
  simp only [Bool.false_eq_true,if_false]
  have h := encode_flatten_blocks
    (List.ofFn (fun i : Fin capacity => tickBoundedSymbolBlocks tm capacity input inputStride outputBase bound false stack i))
    (fun xs : List Bool => xs)
  simpa [tickBoundedStackBlocks,List.map_ofFn,Function.comp_def,List.map_id] using h.symm

theorem tickSymbolRowAscendingBytes_bounded (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (stack : tm.K) :
    tickSymbolRowAscendingBytes tm stack inputStride bound true input capacity outputBase 0 capacity =
      (tickBoundedStackBlocks tm capacity input inputStride outputBase bound true stack).reverse.flatten := by
  rw [tickSymbolRowAscendingBytes_ofFn]
  simp only [Nat.zero_add]
  simp_rw [tickSymbolRowPayload_bounded]
  simp only [if_true]
  have h := encode_reverse_flatten_blocks
    (List.ofFn (fun i : Fin capacity => tickBoundedSymbolBlocks tm capacity input inputStride outputBase bound true stack i))
    (fun xs : List Bool => xs)
  simpa [tickBoundedStackBlocks,List.map_ofFn,Function.comp_def,List.map_id] using h.symm

theorem tickCellSymbolicPayload_bounded (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) :
    tickCellSymbolicPayload tm inputStride bound backward input capacity outputBase =
      (if backward then (tickBoundedCellBlocks tm capacity input inputStride outputBase bound backward).reverse
       else tickBoundedCellBlocks tm capacity input inputStride outputBase bound backward).flatten := by
  cases backward with
  | false =>
    unfold tickCellSymbolicPayload
    simp only [Bool.false_eq_true,if_false]
    simp_rw [tickSymbolRowDescendingBytes_bounded]
    have h := encode_flatten_blocks
      (List.ofFn (fun k : Fin (Fintype.card tm.K) => tickBoundedStackBlocks tm capacity input inputStride outputBase bound false
        ((Fintype.equivFin tm.K).symm k))) (fun xs : List Bool => xs)
    simpa [tickBoundedCellBlocks,tickStackOrder,List.map_ofFn,Function.comp_def,List.map_id] using h.symm
  | true =>
    unfold tickCellSymbolicPayload
    simp only [if_true,List.map_reverse]
    simp_rw [tickSymbolRowAscendingBytes_bounded]
    have h := encode_reverse_flatten_blocks
      (List.ofFn (fun k : Fin (Fintype.card tm.K) => tickBoundedStackBlocks tm capacity input inputStride outputBase bound true
        ((Fintype.equivFin tm.K).symm k))) (fun xs : List Bool => xs)
    simpa [tickBoundedCellBlocks,tickStackOrder,List.map_ofFn,Function.comp_def,List.map_id] using h.symm

end ShiReversibleGenerator
