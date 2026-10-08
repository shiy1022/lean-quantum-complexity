import ReversibleRawWorkEmbedding

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversible ShiReversibleGateBridge

theorem boundProgram_append (n : Nat) (xs ys : List RawAssignment)
    (ht : ∀ a ∈ xs++ys,a.target<n) (hp : ∀ a ∈ xs++ys,a.Topological) :
    boundProgram n (xs++ys) ht hp=
      boundProgram n xs (fun a ha => ht a (List.mem_append_left ys ha))
        (fun a ha => hp a (List.mem_append_left ys ha))++
      boundProgram n ys (fun a ha => ht a (List.mem_append_right xs ha))
        (fun a ha => hp a (List.mem_append_right xs ha)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.cons_append,boundProgram_cons]
    rw [ih]

/-- Exact compiler concatenation retains the semantic node order in the final physical wire supply. -/
theorem compileAssignments_boundProgram_append (n : Nat) (xs ys : List RawAssignment)
    (ht : ∀ a ∈ xs++ys,a.target<n) (hp : ∀ a ∈ xs++ys,a.Topological) :
    compileAssignments (boundProgram n (xs++ys) ht hp)=
      compileAssignments (boundProgram n xs (fun a ha => ht a (List.mem_append_left ys ha))
        (fun a ha => hp a (List.mem_append_left ys ha)))++
      compileAssignments (boundProgram n ys (fun a ha => ht a (List.mem_append_right xs ha))
        (fun a ha => hp a (List.mem_append_right xs ha))) := by
  rw [boundProgram_append]
  exact List.flatMap_append

/-- Original natural-address serialization distributes over concatenation in both forward and inverse quantum orders. -/
theorem rawProgramPayload_append (backward : Bool) (xs ys : List RawAssignment) :
    (((if backward then (xs++ys).reverse else xs++ys).map (rawAssignmentPayload backward)).flatten)=
      if backward then
        ((ys.reverse.map (rawAssignmentPayload backward)).flatten)++
          ((xs.reverse.map (rawAssignmentPayload backward)).flatten)
      else ((xs.map (rawAssignmentPayload backward)).flatten)++
        ((ys.map (rawAssignmentPayload backward)).flatten) := by
  cases backward <;> simp [List.map_append,List.flatten_append,List.reverse_append]

end ShiReversibleGenerator
