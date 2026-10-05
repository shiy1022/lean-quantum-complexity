import «BQP-typed-polytime»
import «BQP-skip-headers»
import «BQP-circuit-pass-outputs»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace BQPFamilyPasses
open Turing Polynomial

/-- The uniform generator is a typed computation of the input length encoded
by the actual family description. No decoder hypothesis is introduced. -/
theorem description_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (ShiBQP.encFamilyAt F) List.length) := by
  obtain ⟨g,hg,he⟩ := BQPChecked.reference22.1 F hu
  obtain ⟨A⟩ := hg
  exact ⟨{ A with outputsFun := fun x => by simpa only [he, id_eq] using A.outputsFun x }⟩

theorem circuit_suffix (F : ShiClass.Family) (n : ℕ) :
    BQPSkipHeaders.dropHeader (BQPSkipHeaders.dropHeader (ShiBQP.encFamilyAt F n)) =
      ShiBQP.encCirc (F.circ n) := by
  simpa only [ShiBQP.encFamilyAt, ShiBQP.encNat, List.append_assoc,
    List.singleton_append, List.cons_append, List.nil_append] using BQPSkipHeaders.two_unary (F.anc n) (F.out n).val
      (ShiBQP.encCirc (F.circ n))

/-- Strip the two actual family headers, using the already proved total machine. -/
theorem strip_polyTime (F : ShiClass.Family) :
    Nonempty (TM2ComputableInPolyTime (ShiBQP.encFamilyAt F)
      (fun n => ShiBQP.encCirc (F.circ n)) id) := by
  obtain ⟨A⟩ := BQPSkipHeaders.polyTime
  refine ⟨{ A with outputsFun := ?_ }⟩
  intro n
  simpa only [id_eq, circuit_suffix] using A.outputsFun (ShiBQP.encFamilyAt F n)

theorem circuit_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) (fun n => ShiBQP.encCirc (F.circ n))
      List.length) := by
  have h := BQPTypedPolyTime.comp (description_polyTime F hu) (strip_polyTime F)
  exact h

/-- One fixed machine handles every wire count of the family. -/
theorem forward_typed (C : BQPProgram.Checker) (F : ShiClass.Family) :
    Nonempty (TM2ComputableInPolyTime (fun n => ShiBQP.encCirc (F.circ n)) id
      (fun n => C.encode (BQPProgram.forwardBody (F.circ n).flatten))) := by
  refine ⟨{ tm := BQPCircuitPass.machine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.C 3 * X
            outputsFun := ?_ }⟩
  intro n
  have h := BQPCircuitPass.outputs C (F.circ n)
  have ht := h.steps_le_m.trans (BQPCircuitPass.cost_le (F.circ n))
  simpa only [TM2OutputsInTime, id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl,
    List.map_id, eval_mul, eval_C, eval_X] using
    ({ h with steps_le_m := ht } : TM2OutputsInTime _ _ _ (3 * (ShiBQP.encCirc (F.circ n)).length))

theorem adjoint_typed (C : BQPProgram.Checker) (F : ShiClass.Family) :
    Nonempty (TM2ComputableInPolyTime (fun n => ShiBQP.encCirc (F.circ n)) id
      (fun n => C.encode (BQPProgram.adjointBody (F.circ n).flatten))) := by
  refine ⟨{ tm := BQPAdjointPass.machine
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := Polynomial.C 64 * X + Polynomial.C 1
            outputsFun := ?_ }⟩
  intro n
  have h := BQPAdjointPass.outputs C (F.circ n)
  have ht := h.steps_le_m.trans (BQPAdjointPass.cost_le C (F.circ n))
  simpa only [TM2OutputsInTime, id_eq, Equiv.refl_symm, Equiv.invFun_as_coe, Equiv.coe_refl,
    List.map_id, eval_add, eval_mul, eval_C, eval_X] using
    ({ h with steps_le_m := ht } : TM2OutputsInTime _ _ _ (64 * (ShiBQP.encCirc (F.circ n)).length + 1))

/-- Actual polynomial-time family forward compilation from arbitrary input strings. -/
theorem forward_polyTime (C : BQPProgram.Checker) (F : ShiClass.Family)
    (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeComputable (fun x => C.encode (BQPProgram.forwardBody (F.circ x.length).flatten)) := by
  have h := BQPTypedPolyTime.comp (circuit_polyTime F hu) (forward_typed C F)
  exact h

/-- Actual polynomial-time family adjoint compilation, including reversal. -/
theorem adjoint_polyTime (C : BQPProgram.Checker) (F : ShiClass.Family)
    (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeComputable (fun x => C.encode (BQPProgram.adjointBody (F.circ x.length).flatten)) := by
  have h := BQPTypedPolyTime.comp (circuit_polyTime F hu) (adjoint_typed C F)
  exact h

end BQPFamilyPasses
