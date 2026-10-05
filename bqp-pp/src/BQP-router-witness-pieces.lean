import «BQP-router-threshold-polytime»
import «BQP-unary-split»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BQPRouterArithmetic
open Turing BQPProgram

/-- The split count 2h is constructed in unary from the actual family. -/
theorem family_split_count_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    PvsNP.PolyTimeComputable (fun x => List.replicate (2*(familyH F x+1)) true) := by
  have hp : PvsNP.PolyTimeComputable (fun x => List.replicate (familyH F x+1) true) := by
    simpa only [PvsNP.PolyTimeComputable, Function.comp_def, List.replicate_succ] using
      BQPTypedPolyTime.comp (BQPOpcodeCount.family_polyTime F hu)
        (BQPStringPrimitives.prefix_polyTime true)
  have h := BQPJoint.polyTimeComputable_append _ _ hp hp
  simpa only [← List.replicate_add, two_mul] using h

/-- Both witness pieces are computed for every pair, including short witnesses.
This theorem computes a piece alone; retaining the original instance for dispatch
is a separate assembly step. -/
theorem family_witness_piece_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F)
    (keep : Bool) : Nonempty (TM2ComputableInPolyTime PvsNP.encodePair id
      (fun p : List Bool × List Bool => BQPUnarySplit.result keep (2*(familyH F p.1+1)) p.2)) := by
  have h1 := BQPMapFirst.map_first_polyTime _ (family_split_count_polyTime F hu)
  have h2 := BQPGeneralPolyTime.comp (Sum.inl false) h1 (BQPUnarySplit.polyTime keep)
  simpa only [Function.comp_def, List.length_replicate] using h2

theorem family_inner_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    Nonempty (TM2ComputableInPolyTime PvsNP.encodePair id
      (fun p : List Bool × List Bool => p.2.take (2*(familyH F p.1+1)))) :=
  family_witness_piece_polyTime F hu true

theorem family_suffix_polyTime (F : ShiClass.Family) (hu : ShiBQP.Uniform F) :
    Nonempty (TM2ComputableInPolyTime PvsNP.encodePair id
      (fun p : List Bool × List Bool => p.2.drop (2*(familyH F p.1+1)))) :=
  family_witness_piece_polyTime F hu false

end BQPRouterArithmetic
