import «AMPUNI-copy-parser-bounds»
import «AMPUNI-payload-copy-valid-run»
import «AMPUNI-first-payload-valid-run»
import «AMPUNI-piece-controller-cost-bound»

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
namespace ShiTMCopyStageCost
open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController ShiTMPieceSchedule
open ShiTMRetainedPayload ShiTMParserCost

noncomputable def mirrorCost (copy : Fin 3) (F : ShiClassQMA.QMAFamily) (n : Nat) : Nat :=
  let ps := expectedPieces copy n (F.wit n) (F.anc n)
  (2 * (pieceCells Prod.fst ps).length + 3) +
    (2 * (pieceCells Prod.snd ps).length + 3)

noncomputable def firstCost (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k)) : Nat :=
  ShiTMReplayTableClear.clearCost V + 1 +
    (scheduleCost n (F.wit n) (F.anc n) (program 0) + 1) + 1 +
    mirrorCost 0 F n + 1 + layerCopyCost 0 F n

noncomputable def replayCost (copy : Fin 3) (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k)) : Nat :=
  ShiTMReplayCycle.cycleCost (F.out n : Nat)
    ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit) + 1 +
    ShiTMReplayHeaderSkip.skipCost n (F.wit n) (F.anc n) (F.out n : Nat) + 1 +
    ShiTMReplayTableClear.clearCost V + 1 +
    (scheduleCost n (F.wit n) (F.anc n) (program copy) + 1) + 1 +
    mirrorCost copy F n + 1 + copyCost copy F n

/-- The old table/mirror contents are the only initial-state-dependent cost.
All newly constructed data is bounded by the original Boolean input length. -/
def stageBound (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k)) : Nat :=
  ShiTMReplayTableClear.clearCost V +
    (600 * inputLength F n + 400) * inputLength F n + 400

theorem mirrorCost_le (copy : Fin 3) (F : ShiClassQMA.QMAFamily) (n : Nat) :
    mirrorCost copy F n ≤ 80 * inputLength F n + 6 := by
  let ps := expectedPieces copy n (F.wit n) (F.anc n)
  have ha : (pieceCells Prod.fst ps).length ≤ tableSize ps := by
    simpa only [piece_cells_length] using pieces_le ps
  have hb : (pieceCells Prod.snd ps).length ≤ tableSize ps := by
    simpa only [piece_cells_length] using bases_le ps
  have ht : tableSize ps ≤ 20 * inputLength F n :=
    expected_table_size_le_inputLength copy F n
  change (2 * (pieceCells Prod.fst ps).length + 3) +
    (2 * (pieceCells Prod.snd ps).length + 3) ≤ _
  omega

theorem programCost_le_inputLength (copy : Fin 3) (F : ShiClassQMA.QMAFamily) (n : Nat) :
    scheduleCost n (F.wit n) (F.anc n) (program copy) ≤ 128 * inputLength F n + 256 := by
  have hp := programCost_le copy n (F.wit n) (F.anc n)
  have hs := resources_le_inputLength F n
  omega

theorem cycleCost_le_inputLength (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ShiTMReplayCycle.cycleCost (F.out n : Nat)
      ((ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit) ≤
        4 * inputLength F n + 6 := by
  have ho := output_index_le_inputLength F n
  simp only [ShiTMReplayCycle.cycleCost, List.length_map]
  change _ ≤ 4 * (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).length + 6
  dsimp only [inputLength] at ho
  omega

theorem skipCost_le_inputLength (F : ShiClassQMA.QMAFamily) (n : Nat) :
    ShiTMReplayHeaderSkip.skipCost n (F.wit n) (F.anc n) (F.out n : Nat) ≤ inputLength F n := by
  rw [inputLength_eq]
  unfold ShiTMReplayHeaderSkip.skipCost
  omega

theorem firstCost_le (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k)) : firstCost F n V ≤ stageBound F n V := by
  have hp := programCost_le_inputLength 0 F n
  have hm := mirrorCost_le 0 F n
  have hb := layerCopyCost_le 0 F n
  unfold firstCost stageBound
  simp only [Nat.add_mul] at *
  omega

theorem replayCost_le (copy : Fin 3) (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k)) : replayCost copy F n V ≤ stageBound F n V := by
  have hr := cycleCost_le_inputLength F n
  have hs := skipCost_le_inputLength F n
  have hp := programCost_le_inputLength copy F n
  have hm := mirrorCost_le copy F n
  have hb := copyCost_le copy F n
  unfold replayCost stageBound
  simp only [Nat.add_mul] at *
  omega

end ShiTMCopyStageCost
