import ReversibleRawSubstitutionLayers
import ReversibleRegisterFlattening

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversible ShiReversibleGateBridge

/-- Enlarging the physical wire supply leaves every natural address unchanged. -/
theorem rawAssignment_compile_workGate {n m : Nat} (a : RawAssignment)
    (ht : a.target<n) (hp : a.Topological) :
    (a.toAssignment (ht.trans_le (Nat.le_add_right n m)) hp).compile=
      (a.toAssignment ht hp).compile.map workGate := by
  cases a with
  | constant t b => cases b <;> rfl
  | copy s t => rfl
  | neg s t => rfl
  | conj a b t => rfl

theorem rawProgram_compile_workGate {n m : Nat} (nodes : List RawAssignment)
    (ht : ∀ a ∈ nodes,a.target<n) (hp : ∀ a ∈ nodes,a.Topological) :
    compileAssignments (boundProgram (n+m) nodes (fun a ha => (ht a ha).trans_le (Nat.le_add_right n m)) hp)=
      (compileAssignments (boundProgram n nodes ht hp)).map workGate := by
  induction nodes with
  | nil => rfl
  | cons a nodes ih =>
    simp only [boundProgram_cons,compileAssignments,List.flatMap_cons,List.map_append]
    simp only [compileAssignments] at ih
    rw [rawAssignment_compile_workGate,ih]

/-- The same original serialized payload is valid after flattening the separate output register. -/
theorem rawProgramPayload_work_substitute {n m : Nat} (nodes : List RawAssignment)
    (ht : ∀ a ∈ nodes,a.target<n) (hp : ∀ a ∈ nodes,a.Topological)
    (hd : ∀ a ∈ nodes,a.DistinctControls) (backward : Bool) :
    (((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten)=
      ((substitute ((if backward then (compileAssignments (boundProgram n nodes ht hp)).reverse
        else compileAssignments (boundProgram n nodes ht hp)).map (workGate (m := m)))).map ShiBQP.encLayer).flatten := by
  have h := rawProgramPayload_substitute (n+m) nodes
    (fun a ha => (ht a ha).trans_le (Nat.le_add_right n m)) hp hd backward
  rw [rawProgram_compile_workGate] at h
  cases backward <;> simpa only [Bool.false_eq_true,if_false,if_true,List.map_reverse] using h

end ShiReversibleGenerator
