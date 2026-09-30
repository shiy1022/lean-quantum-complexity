import «AMPUNI-parser-cost-bounds»
import «AMPUNI-retained-layer-copy-pass»
import «AMPUNI-retained-payload-copy-pass»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace ShiTMRetainedPayload
open ShiTMLayoutMachine ShiTMOuterLift ShiTMPieceController ShiTMParserCost

def inputLength (F : ShiClassQMA.QMAFamily) (n : Nat) : Nat :=
  (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).length

theorem inputLength_eq (F : ShiClassQMA.QMAFamily) (n : Nat) :
    inputLength F n = n + F.wit n + F.anc n + (F.out n : Nat) +
      (F.circ n).length + 5 + ((F.circ n).map ShiBQP.encLayer).flatten.length := by
  simp only [inputLength, ShiClassQMAU.encQMAFamilyAt, ShiBQP.encCirc,
    ShiBQP.encStr, ShiBQP.encNat, List.length_append, List.length_map,
    List.length_replicate, List.length_cons, List.length_nil]
  omega

theorem resources_le_inputLength (F : ShiClassQMA.QMAFamily) (n : Nat) :
    n + F.wit n + F.anc n + 1 ≤ inputLength F n := by
  rw [inputLength_eq]
  omega

theorem output_index_le_inputLength (F : ShiClassQMA.QMAFamily) (n : Nat) :
    (F.out n : Nat) ≤ inputLength F n := by
  rw [inputLength_eq]
  omega

theorem depth_header_le_inputLength (F : ShiClassQMA.QMAFamily) (n : Nat) :
    (F.circ n).length + 1 ≤ inputLength F n := by
  rw [inputLength_eq]
  omega

theorem payload_length_le_inputLength (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ((F.circ n).map ShiBQP.encLayer).flatten.length ≤ inputLength F n := by
  rw [inputLength_eq]
  omega

theorem expected_table_size_le (copy : Fin 3) (n w a : Nat) :
    tableSize (expectedPieces copy n w a) ≤ 20 * (n+w+a+1) := by
  fin_cases copy
  · simpa [expectedPieces] using copy0_table_size_le n w a
  · simpa [expectedPieces] using copy1_table_size_le n w a
  · simpa [expectedPieces] using copy2_table_size_le n w a

theorem expected_table_size_le_inputLength (copy : Fin 3)
    (F : ShiClassQMA.QMAFamily) (n : Nat) :
    tableSize (expectedPieces copy n (F.wit n) (F.anc n)) ≤ 20 * inputLength F n :=
  (expected_table_size_le copy n (F.wit n) (F.anc n)).trans
    (Nat.mul_le_mul_left 20 (resources_le_inputLength F n))

/-- The first copy's exact layer-loop cost is quadratic in the actual retained
Boolean input length, with no separate size or mirror hypotheses. -/
theorem layerCopyCost_le (copy : Fin 3) (F : ShiClassQMA.QMAFamily) (n : Nat) :
    layerCopyCost copy F n ≤ (600 * inputLength F n + 86) * inputLength F n + 1 := by
  unfold layerCopyCost
  apply layer_cost_with_mirrors_le_quadratic
  · exact expected_table_size_le_inputLength copy F n
  · have he := sourceLayers_typed_zero (expectedPieces copy n (F.wit n) (F.anc n))
      (by simp [expectedPieces_width]) (F.circ n)
    rw [he, List.length_map]
    exact payload_length_le_inputLength F n

/-- Replayed copies additionally scan their original local depth header. -/
theorem copyCost_le (copy : Fin 3) (F : ShiClassQMA.QMAFamily) (n : Nat) :
    copyCost copy F n ≤ (600 * inputLength F n + 87) * inputLength F n + 1 := by
  have hcost : copyCost copy F n = (F.circ n).length + 1 + layerCopyCost copy F n := rfl
  have hp := layerCopyCost_le copy F n
  have hd := depth_header_le_inputLength F n
  rw [hcost]
  simp only [Nat.add_mul] at *
  omega

end ShiTMRetainedPayload
