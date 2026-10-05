import «BQP-pair-codec»
import «BQP-pair-generation»

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BQPPairFanout
open Turing

theorem pair_polyTime (f g : List Bool × List Bool → List Bool)
    (hf : Nonempty (TM2ComputableInPolyTime PvsNP.encodePair id f))
    (hg : Nonempty (TM2ComputableInPolyTime PvsNP.encodePair id g)) :
    Nonempty (TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair
      (fun p => (f p,g p))) := by
  have h1 := BQPGeneralPolyTime.comp (Sum.inl false) BQPPairCodec.decode_polyTime hf
  have h2 := BQPGeneralPolyTime.comp (Sum.inl false) BQPPairCodec.decode_polyTime hg
  have h3 := BQPPairGeneration.pair_polyTime _ _ h1 h2
  have h4 := BQPGeneralPolyTime.comp false BQPPairCodec.encode_polyTime h3
  simpa only [Function.comp_def, BQPPairCodec.decode_encode] using h4

/-- A tagged checker becomes a total Boolean-string computation via the concrete decoder. -/
theorem checker_strings (R : List Bool × List Bool → Bool) (hR : PvsNP.PolyTimeChecker R) :
    PvsNP.PolyTimeComputable (fun s => [R (BQPPairCodec.decode s)]) := by
  obtain ⟨A⟩ := BQPGeneralPolyTime.comp (Sum.inl false) BQPPairCodec.decode_polyTime hR
  refine ⟨{ A with outputsFun := ?_ }⟩
  intro s
  simpa only [Function.comp_def, Computability.encodeBool, List.pure_def, id_eq] using A.outputsFun s

end BQPPairFanout
