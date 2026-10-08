import ReversibleExtractionDisjoinPasses
import ReversibleFixedFormulaPrinter

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula
variable {ι : Type}

/-- The original false constant requires zero elementary layers on its initially zero fresh wire. -/
theorem rawAssignmentPayload_false (backward : Bool) (target : Nat) :
    rawAssignmentPayload backward (.constant target false)=[] := rfl

theorem disjoin_forward_payload_passes (ps : List (Formula ι)) (inputs : ι → Nat) (base : Nat) :
    (((disjoin ps).rawCompile inputs base).map (rawAssignmentPayload false)).flatten=
      ((disjoinTermPrefix inputs base ps).map (rawAssignmentPayload false)).flatten ++
      ((disjoinClosingSuffix base (base+(ps.map (fun p => p.size+4)).sum) ps).map
        (rawAssignmentPayload false)).flatten := by
  rw [disjoin_rawCompile_passes]
  simp only [List.map_append,List.flatten_append,List.map_cons,List.map_nil,
    rawAssignmentPayload_false,List.flatten_cons,List.flatten_nil,List.nil_append,List.append_nil]

theorem disjoin_inverse_payload_passes (ps : List (Formula ι)) (inputs : ι → Nat) (base : Nat) :
    ((((disjoin ps).rawCompile inputs base).reverse).map (rawAssignmentPayload true)).flatten=
      (((disjoinClosingSuffix base (base+(ps.map (fun p => p.size+4)).sum) ps).reverse).map
        (rawAssignmentPayload true)).flatten ++
      (((disjoinTermPrefix inputs base ps).reverse).map (rawAssignmentPayload true)).flatten := by
  rw [disjoin_rawCompile_passes]
  simp only [List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,
    List.map_append,List.flatten_append,List.map_cons,List.map_nil,
    rawAssignmentPayload_false,List.flatten_cons,List.flatten_nil,List.nil_append,List.append_nil,List.append_assoc]

end ShiReversibleGenerator
