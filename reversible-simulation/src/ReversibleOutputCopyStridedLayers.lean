import ReversibleOutputCopyLoopCircuitCertificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Copy the roots of successive padded extraction blocks into increasing output positions. -/
noncomputable def stridedOutputCopyLayers (wires sourceBase stride outputBase count : Nat)
    (hstride : 0 < stride) (hend : sourceBase+count*stride ≤ outputBase)
    (hout : outputBase+count ≤ wires) : ShiShallow.Layered wires :=
  List.ofFn (fun j : Fin count =>
    let hs : sourceBase+(j.val+1)*stride-1 < outputBase := by
      have hm : (j.val+1)*stride ≤ count*stride := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt j.isLt)
      have hp : 0 < (j.val+1)*stride := Nat.mul_pos (Nat.succ_pos j.val) hstride
      omega
    [.cnot ⟨sourceBase+(j.val+1)*stride-1,by have hj := j.isLt; omega⟩
      ⟨outputBase+j.val,by have hj := j.isLt; omega⟩ (by
        intro he
        have hv := congrArg Fin.val he
        dsimp only at hv
        omega)])

/-- The actual retreating pointer generator prints exactly the increasing padded-root copy circuit. -/
theorem outputCopyQuantumLayers_strided (wires sourceBase stride outputBase count : Nat)
    (hstride : 0 < stride) (hbase : 0 < outputBase) (hend : sourceBase+count*stride ≤ outputBase)
    (hout : outputBase+count ≤ wires) :
    outputCopyQuantumLayers wires outputBase stride count (sourceBase+count*stride-1) (by omega) hout=
      stridedOutputCopyLayers wires sourceBase stride outputBase count hstride hend hout := by
  induction count with
  | zero => simp [outputCopyQuantumLayers,stridedOutputCopyLayers]
  | succ k ih =>
      have hk : sourceBase+k*stride ≤ outputBase := by
        have hm : k*stride ≤ (k+1)*stride := Nat.mul_le_mul_right stride (Nat.le_succ k)
        omega
      have ho : outputBase+k ≤ wires := by omega
      have hp : sourceBase+(k+1)*stride-1-stride=sourceBase+k*stride-1 := by
        rw [Nat.succ_mul,Nat.sub_sub]
        omega
      simp only [outputCopyQuantumLayers,hp,ih hk ho]
      simp only [stridedOutputCopyLayers,List.ofFn_succ',List.concat_eq_append,Fin.val_castSucc,Fin.val_last]

end ShiReversibleGenerator
