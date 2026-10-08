import ReversibleExtractionDisjoinPayloadPasses
import ReversiblePaddedFormula

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula
variable {ι : Type}

/-- Fresh false padding contributes no elementary quantum instructions, in either direction. -/
theorem falsePadding_payload (backward : Bool) (base count : Nat) :
    ((falsePadding base count).map (rawAssignmentPayload backward)).flatten=[] := by
  simp [falsePadding,List.map_map,Function.comp_def,rawAssignmentPayload_false]

/-- Forward padding is the original formula's exact payload followed by its padded-root copy. -/
theorem paddedFormula_forward_payload (p : Formula ι) (inputs : ι → Nat) (base bound : Nat) :
    ((p.paddedCompile inputs base bound).map (rawAssignmentPayload false)).flatten=
      ((p.rawCompile inputs base).map (rawAssignmentPayload false)).flatten ++
        rawAssignmentPayload false (.copy (p.result base) (base+bound)) := by
  simp only [Formula.paddedCompile,List.map_append,List.flatten_append,falsePadding_payload,
    List.append_nil,List.map_cons,List.map_nil,List.flatten_cons,List.flatten_nil]

/-- Inverse padding starts with the same root CNOT, then reverses the original formula payload. -/
theorem paddedFormula_inverse_payload (p : Formula ι) (inputs : ι → Nat) (base bound : Nat) :
    (((p.paddedCompile inputs base bound).reverse).map (rawAssignmentPayload true)).flatten=
      rawAssignmentPayload true (.copy (p.result base) (base+bound)) ++
        ((p.rawCompile inputs base).reverse.map (rawAssignmentPayload true)).flatten := by
  have hp : (((falsePadding (base+p.size) (bound-p.size)).reverse).map (rawAssignmentPayload true)).flatten=[] := by
    simp [falsePadding,List.map_reverse,List.map_map,Function.comp_def,rawAssignmentPayload_false]
  simp only [Formula.paddedCompile,List.reverse_append,List.reverse_cons,List.reverse_nil,
    List.nil_append,List.map_append,List.flatten_append,hp,List.nil_append,List.map_cons,
    List.map_nil,List.flatten_cons,List.flatten_nil,List.append_nil]

end ShiReversibleGenerator
