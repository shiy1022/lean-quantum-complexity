import «AMPUNI-copy-stage-cost-bounds»
import «AMPUNI-finite-stack-growth»
import «AMPUNI-prepared-readout»
import «AMPUNI-global-fanout-prefix-bounds»

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ShiTMCopyStageCost
open ShiTMRetainedTop ShiTMRetainedPayload ShiTMStackGrowth

theorem stack_length_le_size (V : ∀ k, List (TopGam k)) (j : TopK) :
    (V j).length ≤ size V := by
  exact Finset.single_le_sum (f := fun k => (V k).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

/-- Old work tables can be charged to the total intermediate stack size. -/
theorem clearCost_le_size (V : ∀ k, List (TopGam k)) :
    ShiTMReplayTableClear.clearCost V ≤ 4 * size V + 4 := by
  have h1 := stack_length_le_size V (ShiTMReplayTableClear.stack .width)
  have h2 := stack_length_le_size V (ShiTMReplayTableClear.stack .base)
  have h8 := stack_length_le_size V (ShiTMReplayTableClear.stack .widthMirror)
  have h9 := stack_length_le_size V (ShiTMReplayTableClear.stack .baseMirror)
  unfold ShiTMReplayTableClear.clearCost
  omega

theorem stageBound_le_size (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k)) :
    stageBound F n V ≤ 4 * size V +
      (600 * inputLength F n + 400) * inputLength F n + 404 := by
  have h := clearCost_le_size V
  unfold stageBound
  omega

theorem prefixCost_le_size (F : ShiClassQMA.QMAFamily) (n : Nat)
    (V : ∀ k, List (TopGam k)) :
    (F.circ n).length + 2 + ShiTMFanoutStage.stageCost n (F.wit n) (F.anc n) V ≤
      3 * size V + 82 * inputLength F n * inputLength F n := by
  have hd : (F.circ n).length ≤ inputLength F n :=
    Nat.le_trans (Nat.le_succ _) (depth_header_le_inputLength F n)
  have h := ShiTMGlobalFanoutPrefix.prefix_cost_le n (F.wit n) (F.anc n)
    (F.circ n).length (inputLength F n) V (resources_le_inputLength F n) hd
  have h0 := stack_length_le_size V (ShiTMFanoutPrepare.port 0)
  have h1 := stack_length_le_size V (ShiTMFanoutPrepare.port 1)
  have h2 := stack_length_le_size V (ShiTMFanoutPrepare.port 2)
  unfold ShiTMFanoutStage.workSize at h
  omega

theorem readoutCopyCost_le_size (copy : Fin 3) (F : ShiClassQMA.QMAFamily)
    (n : Nat) (V : ∀ k, List (TopGam k)) :
    ShiTMReadoutCopy.copyCost copy n (F.wit n) (F.anc n) (F.out n) V ≤
      4 * size V + 415 * inputLength F n := by
  have h := ShiTMReadoutCopy.copyCost_le copy n (F.wit n) (F.anc n)
    (F.out n) (inputLength F n) V (resources_le_inputLength F n) (F.out n).isLt
  have h0 := stack_length_le_size V (ShiTMReadoutCopy.core 0)
  have h1 := stack_length_le_size V (ShiTMReadoutCopy.core 1)
  have h2 := stack_length_le_size V (ShiTMReadoutCopy.core 2)
  have hd := stack_length_le_size V (ShiTMReadoutCopy.destination copy)
  unfold ShiTMReadoutCopy.initialWorkSize at h
  omega

theorem readoutScratchCost_le_size (F : ShiClassQMA.QMAFamily)
    (n : Nat) (V : ∀ k, List (TopGam k)) :
    ShiTMReadoutScratch.cost n (F.wit n) (F.anc n) V ≤
      4 * size V + 30 * inputLength F n := by
  have h := ShiTMReadoutScratch.cost_le n (F.wit n) (F.anc n)
    (inputLength F n) V (resources_le_inputLength F n)
  have h0 := stack_length_le_size V (ShiTMReadoutScratch.core 0)
  have h1 := stack_length_le_size V (ShiTMReadoutScratch.core 1)
  have h2 := stack_length_le_size V (ShiTMReadoutScratch.core 2)
  have h7 := stack_length_le_size V (ShiTMReadoutScratch.core 7)
  omega

/-- The remaining readout overhead is linear in the four intermediate sizes
and the original input length. Stack-growth bounds can eliminate those sizes. -/
theorem preparedReadoutCost_le_size (F : ShiClassQMA.QMAFamily) (n : Nat)
    (S A B C : ∀ k, List (TopGam k)) :
    ShiTMPreparedReadout.stageCost n (F.wit n) (F.anc n) (F.out n) S A B C ≤
      4 * (size S + size A + size B + size C) + 4906 * inputLength F n + 4 := by
  have h0 := readoutCopyCost_le_size 0 F n S
  have h1 := readoutCopyCost_le_size 1 F n A
  have h2 := readoutCopyCost_le_size 2 F n B
  have hs := readoutScratchCost_le_size F n C
  have he := ShiTMReadout.family_readout_cost_le F n
  change _ ≤ 3631 * inputLength F n at he
  unfold ShiTMPreparedReadout.stageCost
  omega

end ShiTMCopyStageCost
