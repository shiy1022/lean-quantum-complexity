import «BQP-family-fields»
import «BQP-bit-blocks-outputs»
import «BQP-joint-output»
import «BQP-map-first-integration»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace BQPFamilyPasses
open Turing BQPProgram

theorem paddedInput_eq (x : List Bool) (m : ℕ) :
    paddedInput m (ShiBQP.toBits x) = x ++ List.replicate m false := by
  rw [paddedInput, List.ofFn_fin_append, List.ofFn_const]
  change List.ofFn (x.get) ++ List.replicate m false = _
  rw [List.ofFn_get]

theorem padded_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeComputable (fun x => paddedInput (F.anc x.length+1) (ShiBQP.toBits x)) := by
  simp only [paddedInput_eq]
  exact BQPJoint.polyTimeComputable_append id _
    ⟨idComputableInPolyTime (id : List Bool → List Bool)⟩ (padding_polyTime F hu)

/-- The exact seven-piece string consumed by the opcode checker, in its reversed
program encoding order. -/
theorem encoded_family_eq (C : Checker) (F : ShiClass.Family) (x : List Bool) :
    C.encode (familyProgram F x) =
      C.encode (List.replicate (x.length+F.anc x.length+1) 0) ++
      (C.encode (endpoint (paddedInput (F.anc x.length+1) (ShiBQP.toBits x))) ++
      (C.encode (adjointBody (F.circ x.length).flatten) ++
      (C.encode (wrap (F.out x.length).val [8]) ++
      (C.encode (forwardBody (F.circ x.length).flatten) ++
      (C.encode (List.replicate (x.length+F.anc x.length+1) 0) ++
       C.encode (load (paddedInput (F.anc x.length+1) (ShiBQP.toBits x)))))))) := by
  simp only [familyProgram, compile, checker_encode_eq, BQPOpcodeEmission.encode_append,
    List.append_assoc, Nat.add_assoc]

/-- A concrete polynomial-time compiler for the actual uniform family.
All parsing, circuit passes, padding and concatenation are proved constructions. -/
theorem compiler_polyTime (C : Checker) (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeComputable (fun x => C.encode (familyProgram F x)) := by
  have hp := padded_polyTime F hu
  have hl := BQPTypedPolyTime.comp hp (load_polyTime C)
  have he := BQPTypedPolyTime.comp hp (endpoint_polyTime C)
  have hr : PvsNP.PolyTimeComputable
      (fun x => C.encode (List.replicate (x.length+F.anc x.length+1) 0)) := by
    simpa only [PvsNP.PolyTimeComputable, Function.comp_def, paddedInput_eq, List.length_append,
      List.length_replicate, Nat.add_assoc] using BQPTypedPolyTime.comp hp (return_polyTime C)
  have hf := forward_polyTime C F hu
  have ha := adjoint_polyTime C F hu
  have ho := output_test_polyTime C F hu
  simp only [encoded_family_eq]
  exact BQPJoint.polyTimeComputable_append _ _ hr
    (BQPJoint.polyTimeComputable_append _ _ he
      (BQPJoint.polyTimeComputable_append _ _ ha
        (BQPJoint.polyTimeComputable_append _ _ ho
          (BQPJoint.polyTimeComputable_append _ _ hf
            (BQPJoint.polyTimeComputable_append _ _ hr hl)))))

/-- Witness preservation is now instantiated with the constructed family compiler. -/
theorem familyPreprocess_polyTime (C : Checker) (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    Nonempty (TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair (familyPreprocess C F)) :=
  familyPreprocess_polyTime_of_compiler C F (compiler_polyTime C F hu)

theorem normalized_family_polyTime (C : Checker) (F : ShiClass.Family) (hu : ShiBQP.Uniform F)
    (d : ℕ) : PvsNP.PolyTimeChecker (BQPCounting.pairedPrefix (familyResidue C F d)) :=
  normalized_family_polyTime_of_compiler C F d (compiler_polyTime C F hu)

end BQPFamilyPasses
