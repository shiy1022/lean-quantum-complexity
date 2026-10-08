import ReversibleOutputCopyStridedLayers

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Established CNOT encoding depends only on the raw addresses, not on the containing physical wire supply or its bound proofs. -/
theorem stridedOutputCopyLayers_encoding (wires sourceBase stride outputBase count : Nat)
    (hstride : 0<stride) (hend : sourceBase+count*stride ≤ outputBase)
    (hout : outputBase+count ≤ wires) :
    ((stridedOutputCopyLayers wires sourceBase stride outputBase count hstride hend hout).map ShiBQP.encLayer).flatten=
      (List.ofFn (fun j : Fin count => ShiBQP.encNat 1++ShiBQP.encNat 4++
        ShiBQP.encNat (sourceBase+(j.val+1)*stride-1)++ShiBQP.encNat (outputBase+j.val))).flatten := by
  simp [stridedOutputCopyLayers,List.map_ofFn,Function.comp_def,ShiBQP.encLayer,ShiBQP.encStr,
    ShiBQP.encInstr,List.append_assoc]

end ShiReversibleGenerator
