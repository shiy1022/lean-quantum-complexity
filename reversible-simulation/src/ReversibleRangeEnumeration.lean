import Mathlib.Data.List.OfFn

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {α : Type}

/-- Runtime natural-index traversal has the same order as the established finite enumeration. -/
theorem map_range_ofFn (count : Nat) (f : Nat → α) :
    (List.range count).map f = List.ofFn (fun i : Fin count => f i.val) := by
  induction count generalizing f with
  | zero => simp
  | succ count ih =>
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, List.ofFn_succ]
    congr 1
    simpa only [Function.comp_def, Fin.val_succ] using ih (fun j => f (j + 1))

end ShiReversibleGenerator
