import ReversibleTickLoopTemplatePayload
import ReversiblePaddedForestPayloadEnumeration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The canonical padded tick forest, indexed by the established configuration codec. -/
noncomputable def tickForestPayloadBlocks (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) : List (List Bool) :=
  List.ofFn (fun i : Fin (configurationWidth tm capacity) =>
    let nodes := ((tickFormulas (FormulaCfg.inputs tm capacity)).bitFormula i).paddedCompile
      (fun j => input+inputStride*j.val) (outputBase+i.val*(bound+1)) bound
    ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten)

/-- Forward and reverse emission reverse both forest blocks and assignments inside each block. -/
theorem tickForest_payload_blocks (tm : Turing.FinTM2) (capacity input inputStride outputBase bound : Nat)
    (backward : Bool) :
    ((if backward then (paddedForestCompile (fun j => input+inputStride*j.val) outputBase bound (tickForest tm capacity)).reverse
      else paddedForestCompile (fun j => input+inputStride*j.val) outputBase bound (tickForest tm capacity)).map
      (rawAssignmentPayload backward)).flatten =
      (if backward then (tickForestPayloadBlocks tm capacity input inputStride outputBase bound backward).reverse
       else tickForestPayloadBlocks tm capacity input inputStride outputBase bound backward).flatten := by
  have h := paddedForestPayload_ofFn (tickFormulas (FormulaCfg.inputs tm capacity)).bitFormula
    (fun j => input+inputStride*j.val) outputBase bound backward (rawAssignmentPayload backward)
  cases backward <;> simpa only [tickForest,tickForestPayloadBlocks,Bool.false_eq_true,if_false,if_true] using h

end ShiReversibleGenerator
