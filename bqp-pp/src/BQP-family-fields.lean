import «BQP-family-circuit-passes»
import «BQP-header-field»
import «BQP-skip-one-header»
import «BQP-string-primitives»
import «BQP-unary-block-integration»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BQPFamilyPasses
open Turing

theorem anc_field (F : ShiClass.Family) (n : ℕ) :
    BQPHeaderField.count (ShiBQP.encFamilyAt F n) = F.anc n := by
  simpa only [ShiBQP.encFamilyAt, ShiBQP.encNat, List.append_assoc,
    List.singleton_append, List.cons_append, List.nil_append] using BQPHeaderField.count_unary (F.anc n)
      (ShiBQP.encNat (F.out n).val ++ ShiBQP.encCirc (F.circ n))

theorem out_field (F : ShiClass.Family) (n : ℕ) :
    BQPHeaderField.count (BQPSkipHeaders.dropHeader (ShiBQP.encFamilyAt F n)) = (F.out n).val := by
  simp only [ShiBQP.encFamilyAt, ShiBQP.encNat, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
    BQPSkipHeaders.dropHeader_unary, BQPHeaderField.count_unary]

theorem anc_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeComputable (fun x => List.replicate (F.anc x.length) true) := by
  obtain ⟨A⟩ := BQPHeaderField.polyTime
  have h : Nonempty (TM2ComputableInPolyTime (ShiBQP.encFamilyAt F) id
      (fun n => List.replicate (F.anc n) true)) := by
    refine ⟨{ A with outputsFun := ?_ }⟩
    intro n
    simpa only [id_eq, anc_field] using A.outputsFun (ShiBQP.encFamilyAt F n)
  have hc := BQPTypedPolyTime.comp (description_polyTime F hu) h
  exact hc

theorem out_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeComputable (fun x => List.replicate (F.out x.length).val true) := by
  obtain ⟨A⟩ := BQPTypedPolyTime.comp BQPSkipHeaders.one_polyTime BQPHeaderField.polyTime
  have h : Nonempty (TM2ComputableInPolyTime (ShiBQP.encFamilyAt F) id
      (fun n => List.replicate (F.out n).val true)) := by
    refine ⟨{ A with outputsFun := ?_ }⟩
    intro n
    simpa only [Function.comp_apply, id_eq, out_field] using A.outputsFun (ShiBQP.encFamilyAt F n)
  have hc := BQPTypedPolyTime.comp (description_polyTime F hu) h
  exact hc

theorem output_test_polyTime (C : BQPProgram.Checker) (F : ShiClass.Family)
    (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeComputable (fun x => C.encode (BQPProgram.wrap (F.out x.length).val [8])) := by
  simpa only [PvsNP.PolyTimeComputable, Function.comp_def, List.length_replicate] using
    BQPTypedPolyTime.comp (out_polyTime F hu) (BQPProgram.wrap_polyTime C [8])

/-- The ancilla suffix includes the extra output wire from the original family. -/
theorem padding_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeComputable (fun x => List.replicate (F.anc x.length+1) false) := by
  have hz : PvsNP.PolyTimeComputable (fun x => List.replicate (F.anc x.length) false) := by
    simpa only [PvsNP.PolyTimeComputable, Function.comp_def, List.map_replicate, Equiv.swap_apply_left] using
      BQPTypedPolyTime.comp (anc_polyTime F hu)
        (BQPStringPrimitives.rename_polyTime (Equiv.swap true false))
  simpa only [PvsNP.PolyTimeComputable, Function.comp_def, List.replicate_succ] using
    BQPTypedPolyTime.comp hz (BQPStringPrimitives.prefix_polyTime false)

end BQPFamilyPasses
