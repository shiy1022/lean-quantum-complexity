import «BQP-pair-duplicate»
import «BQP-pair-swap»
import «BQP-general-polytime»

set_option autoImplicit false
namespace BQPPairGeneration
open Turing

theorem map_second_polyTime (g : List Bool → List Bool) (hg : PvsNP.PolyTimeComputable g) :
    Nonempty (TM2ComputableInPolyTime PvsNP.encodePair PvsNP.encodePair
      (fun p : List Bool × List Bool => (p.1,g p.2))) := by
  have h1 := BQPGeneralPolyTime.comp (Sum.inl false) BQPPairSwap.polyTime
    (BQPMapFirst.map_first_polyTime g hg)
  have h2 := BQPGeneralPolyTime.comp (Sum.inl false) h1 BQPPairSwap.polyTime
  exact h2

/-- Evaluate both functions on the same original input and form a genuine tagged pair. -/
theorem pair_polyTime (f g : List Bool → List Bool)
    (hf : PvsNP.PolyTimeComputable f) (hg : PvsNP.PolyTimeComputable g) :
    Nonempty (TM2ComputableInPolyTime id PvsNP.encodePair (fun x => (f x,g x))) := by
  have h1 := BQPGeneralPolyTime.comp (Sum.inl false) BQPPairDuplicate.polyTime
    (BQPMapFirst.map_first_polyTime f hf)
  have h2 := BQPGeneralPolyTime.comp (Sum.inl false) h1 (map_second_polyTime g hg)
  exact h2

end BQPPairGeneration
