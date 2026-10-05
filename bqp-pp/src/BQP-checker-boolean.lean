import «BQP-pair-fanout»
import «BQP-bool-ite»
import «BQP-router-threshold-polytime»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BQPCheckerBoolean
open Turing

theorem constant (b : Bool) : PvsNP.PolyTimeChecker (fun _ => b) := by
  obtain ⟨A⟩ := BQPRouterArithmetic.constant_polyTime [b]
  have hc : PvsNP.PolyTimeDecider (fun _ => b) := by
    refine ⟨{ A with outputsFun := ?_ }⟩
    intro s
    simpa only [Computability.encodeBool, List.pure_def, id_eq] using A.outputsFun s
  have h := BQPGeneralPolyTime.comp false BQPPairCodec.encode_polyTime hc
  exact h

theorem ite (R S T : List Bool × List Bool → Bool)
    (hR : PvsNP.PolyTimeChecker R) (hS : PvsNP.PolyTimeChecker S)
    (hT : PvsNP.PolyTimeChecker T) :
    PvsNP.PolyTimeChecker (fun p => if R p then S p else T p) := by
  have hr := BQPPairFanout.checker_strings R hR
  have hs := BQPPairFanout.checker_strings S hS
  have ht := BQPPairFanout.checker_strings T hT
  have hstream := BQPJoint.polyTimeComputable_append _ _ hr
    (BQPJoint.polyTimeComputable_append _ _ hs ht)
  have hc := BQPGeneralPolyTime.comp false hstream BQPBoolIte.polyTime
  have h := BQPGeneralPolyTime.comp false BQPPairCodec.encode_polyTime hc
  simpa [PvsNP.PolyTimeChecker, Function.comp_def, BQPBoolIte.select,
    BQPPairCodec.decode_encode, List.headI] using h

theorem not (R : List Bool × List Bool → Bool) (hR : PvsNP.PolyTimeChecker R) :
    PvsNP.PolyTimeChecker (fun p => !(R p)) := by
  have h := ite R (fun _ => false) (fun _ => true) hR (constant false) (constant true)
  have he : (fun p => if R p then false else true) = (fun p => !(R p)) := by
    funext p; cases R p <;> rfl
  rwa [he] at h

theorem head_polyTime : PvsNP.PolyTimeDecider (fun s : List Bool => s.headI) := by
  have h := BQPGeneralPolyTime.comp false (BQPStringPrimitives.prefix_polyTime true)
    BQPBoolIte.polyTime
  simpa [PvsNP.PolyTimeDecider, Function.comp_def, BQPBoolIte.select] using h

end BQPCheckerBoolean
