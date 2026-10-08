import ReversibleOutputCopyLoopClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The retreating runtime pointer prints ascending targets in a disjoint output register. -/
noncomputable def outputCopyQuantumLayers (wires outputBase stride : Nat) :
    (count source : Nat) → source < outputBase → outputBase+count ≤ wires → ShiShallow.Layered wires
  | 0, _, _, _ => []
  | k+1, source, hs, ho =>
      outputCopyQuantumLayers wires outputBase stride k (source-stride)
        ((Nat.sub_le _ _).trans_lt hs) (by omega) ++
      [[.cnot ⟨source,by omega⟩ ⟨outputBase+k,by omega⟩ (by
        intro h
        have hv := congrArg Fin.val h
        dsimp only at hv
        omega)]]

theorem outputCopyQuantumLayers_length (wires outputBase stride count source : Nat)
    (hs : source < outputBase) (ho : outputBase+count ≤ wires) :
    (outputCopyQuantumLayers wires outputBase stride count source hs ho).length=count := by
  induction count generalizing source with
  | zero => rfl
  | succ k ih =>
      simp only [outputCopyQuantumLayers,List.length_append,List.length_cons,List.length_nil,ih]

theorem outputCopyQuantumLayers_payload (wires outputBase stride count source : Nat)
    (hs : source < outputBase) (ho : outputBase+count ≤ wires) :
    ((outputCopyQuantumLayers wires outputBase stride count source hs ho).map ShiBQP.encLayer).flatten=
      outputCopyLoopBytes stride count source (outputBase+count-1) := by
  induction count generalizing source with
  | zero => rfl
  | succ k ih =>
      have ht : outputBase+(k+1)-1=outputBase+k := by omega
      rw [ht,outputCopyLoopBytes]
      simp only [outputCopyQuantumLayers,List.map_append,List.flatten_append,ih,List.map_cons,List.map_nil,
        List.flatten_cons,List.flatten_nil,List.append_nil]
      simp [outputCopyLayerBytes,encLayer_singleton,ShiBQP.encInstr]

theorem outputCopyLoopTemplate_quantum_payload (cs : OutputCopyRegister → Nat) (wires outputBase : Nat)
    (hs : cs 0 < outputBase) (ho : outputBase+cs 6 ≤ wires) (ht : cs 1=outputBase+cs 6-1) :
    outputCopyLoopTemplate.bytes cs=
      ((outputCopyQuantumLayers wires outputBase (cs 5) (cs 6) (cs 0) hs ho).map ShiBQP.encLayer).flatten := by
  rw [outputCopyLoopTemplate_payload,ht]
  exact (outputCopyQuantumLayers_payload _ _ _ _ _ hs ho).symm

end ShiReversibleGenerator
