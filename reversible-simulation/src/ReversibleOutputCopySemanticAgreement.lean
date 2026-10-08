import ReversibleOutputCopyResourcePolynomialRun
import ReversibleRegisterFlattening

set_option autoImplicit false
namespace ShiReversibleGenerator

noncomputable def stridedOutputRead (sourceBase stride outputBase count : Nat)
    (hstride : 0 < stride) (hend : sourceBase+count*stride ≤ outputBase) : Fin count → Fin outputBase :=
  fun j => ⟨sourceBase+(j.val+1)*stride-1,by
    have hm : (j.val+1)*stride ≤ count*stride := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt j.isLt)
    have hp : 0 < (j.val+1)*stride := Nat.mul_pos (Nat.succ_pos j.val) hstride
    omega⟩

/-- Flattening and exact gate substitution of the semantic copy block gives one CNOT per output bit. -/
theorem substitute_flat_copyOut {outputBase count : Nat} (read : Fin count → Fin outputBase) :
    ShiReversibleGateBridge.substitute
      ((ShiReversible.copyOut read).map ShiReversibleGateBridge.flatInstruction)=
    (List.finRange count).map (fun j =>
      [ShiShallow.Instr.cnot (Fin.castAdd count (read j)) (Fin.natAdd outputBase j)
        (ShiReversibleGateBridge.left_ne_right (read j) j)]) := by
  have h : ∀ xs : List (Fin count),
      ShiReversibleGateBridge.substitute
        ((xs.map (fun j => ShiReversible.Instruction.copy (read j) j)).map ShiReversibleGateBridge.flatInstruction)=
      xs.map (fun j =>
        [ShiShallow.Instr.cnot (Fin.castAdd count (read j)) (Fin.natAdd outputBase j)
          (ShiReversibleGateBridge.left_ne_right (read j) j)]) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons j xs ih =>
      simpa only [ShiReversibleGateBridge.substitute,List.map_cons,List.flatMap_cons,
        ShiReversibleGateBridge.flatInstruction,ShiReversibleGateBridge.gateCircuit,
        List.cons_append,List.nil_append] using congrArg (fun gs =>
          [ShiShallow.Instr.cnot (Fin.castAdd count (read j)) (Fin.natAdd outputBase j)
            (ShiReversibleGateBridge.left_ne_right (read j) j)]::gs) ih
  exact h _

/-- The finite copy generator's exact quantum block agrees with the semantic clean-circuit copy block. -/
theorem stridedOutputCopyLayers_copyOut (sourceBase stride outputBase count : Nat)
    (hstride : 0 < stride) (hend : sourceBase+count*stride ≤ outputBase) :
    stridedOutputCopyLayers (outputBase+count) sourceBase stride outputBase count hstride hend (Nat.le_refl _)=
      ShiReversibleGateBridge.substitute
        ((ShiReversible.copyOut (stridedOutputRead sourceBase stride outputBase count hstride hend)).map
          ShiReversibleGateBridge.flatInstruction) := by
  rw [substitute_flat_copyOut]
  unfold stridedOutputCopyLayers
  rw [List.ofFn_eq_map]
  apply List.map_congr_left
  intro j hj
  rfl

end ShiReversibleGenerator
