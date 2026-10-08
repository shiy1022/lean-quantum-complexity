import ReversiblePaddedForestEnumeration

set_option autoImplicit false
namespace ShiReversibleFormula
variable {α β ι : Type}

theorem encode_flatten_blocks (blocks : List (List α)) (encode : α → List β) :
    (blocks.flatten.map encode).flatten = (blocks.map (fun block => (block.map encode).flatten)).flatten := by
  induction blocks with
  | nil => rfl
  | cons block rest ih => simp only [List.flatten_cons, List.map_append, List.flatten_append, List.map_cons, ih]

theorem encode_reverse_flatten_blocks (blocks : List (List α)) (encode : α → List β) :
    (blocks.flatten.reverse.map encode).flatten =
      (blocks.map (fun block => (block.reverse.map encode).flatten)).reverse.flatten := by
  induction blocks with
  | nil => rfl
  | cons block rest ih => simp only [List.flatten_cons, List.reverse_append, List.map_append, List.flatten_append, List.map_cons, List.reverse_cons, List.flatten_nil, List.append_nil, List.append_assoc, ih]

/-- Reversing a padded forest reverses both coordinate blocks and the nodes inside every block. -/
theorem paddedForestPayload_ofFn {count : Nat} (forms : Fin count → Formula ι)
    (inputs : ι → Nat) (base bound : Nat) (backward : Bool) (encode : RawAssignment → List β) :
    ((if backward then (paddedForestCompile inputs base bound (List.ofFn forms)).reverse
      else paddedForestCompile inputs base bound (List.ofFn forms)).map encode).flatten =
    (if backward then
      (List.ofFn (fun i => (((forms i).paddedCompile inputs (base + i.val * (bound + 1)) bound).reverse.map encode).flatten)).reverse
    else
      List.ofFn (fun i => (((forms i).paddedCompile inputs (base + i.val * (bound + 1)) bound).map encode).flatten)).flatten := by
  cases backward with
  | false =>
      simp only [Bool.false_eq_true, if_false, paddedForestCompile_ofFn]
      simpa only [List.map_ofFn, Function.comp_def] using encode_flatten_blocks
        (List.ofFn (fun i => (forms i).paddedCompile inputs (base + i.val * (bound + 1)) bound)) encode
  | true =>
      simp only [if_true, paddedForestCompile_ofFn]
      simpa only [List.map_ofFn, Function.comp_def] using encode_reverse_flatten_blocks
        (List.ofFn (fun i => (forms i).paddedCompile inputs (base + i.val * (bound + 1)) bound)) encode

end ShiReversibleFormula
