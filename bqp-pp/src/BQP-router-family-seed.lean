import «BQP-hadamard-code-count»
import «BQP-router-square-root»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BQPRouterArithmetic
open Turing BQPProgram

/-- An existing emitter with two empty blocks supplies a total empty-string machine. -/
theorem empty_polyTime : PvsNP.PolyTimeComputable (fun _ => ([] : List Bool)) := by
  have he : ∀ s : List Bool, BQPBitBlocks.render [] [] s = [] := by
    intro s
    induction s with
    | nil => rfl
    | cons b s ih => cases b <;> simp [BQPBitBlocks.render, ih]
  simpa only [he, BQPOpcodeEmission.encode] using BQPBitBlocks.polyTime [] []

theorem terminator_polyTime : PvsNP.PolyTimeComputable (fun _ => [false]) :=
  BQPTypedPolyTime.comp empty_polyTime (BQPStringPrimitives.prefix_polyTime false)

/-- Unary h+1, with its terminator, is computed from the uniform-family circuit. -/
theorem family_parameter_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeComputable (fun x => ShiBQP.encNat (familyH F x+1)) := by
  have h := BQPTypedPolyTime.comp (BQPOpcodeCount.family_polyTime F hu)
    (BQPStringPrimitives.prefix_polyTime true)
  simpa only [ShiBQP.encNat, List.replicate_succ, Function.comp_def] using
    BQPJoint.polyTimeComputable_append _ _ h terminator_polyTime

/-- Exact square-root seed for the same shifted parameter used by longRelation. -/
theorem family_squareRoot_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeComputable (fun x =>
      bits (familyH F x+1+7) (Nat.sqrt (2*4^(familyH F x+1+3)))) := by
  obtain ⟨A⟩ := family_parameter_polyTime F hu
  have h : Nonempty (TM2ComputableInPolyTime id ShiBQP.encNat (fun x => familyH F x+1)) :=
    ⟨{ A with outputsFun := A.outputsFun }⟩
  have hc := BQPTypedPolyTime.comp h squareRoot_polyTime
  exact hc

end BQPRouterArithmetic
