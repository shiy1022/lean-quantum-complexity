import «AMPUNI-complete-controller-run»
import «AMPUNI-copy-local-embed»

set_option autoImplicit false

open ShiShallow ShiClassQMAAmp

namespace ShiTMCompleteController

open ShiTMLayoutMachine

/-- The first pass's byte chunk is the explicit first embedded verifier copy. -/
theorem firstCopyBytes_eq_embedCirc (F : ShiClassQMA.QMAFamily) (n : Nat)
    (hoff : 0 + (n + (F.wit n + (F.anc n + 1))) ≤
      3 * (n + (F.wit n + (F.anc n + 1))))
    (he : Function.Injective
      (ampE n (F.wit n) (F.anc n) 0 hoff)) :
    firstCopyBytes F n =
      (ShiBQP.encCirc
        (ShiEmbed.embedCirc (ampE n (F.wit n) (F.anc n) 0 hoff)
          he (F.circ n))).map bit := by
  exact congrArg (List.map bit)
    (encode_mapCirc_depth_eq_embedCirc
      n (F.wit n) (F.anc n) 0 hoff he (F.circ n))

/-- The second pass uses the local table for the middle embedded copy. -/
theorem copy1Bytes_eq_embedCirc (F : ShiClassQMA.QMAFamily) (n : Nat)
    (hoff : (n + (F.wit n + (F.anc n + 1))) +
      (n + (F.wit n + (F.anc n + 1))) ≤
      3 * (n + (F.wit n + (F.anc n + 1))))
    (he : Function.Injective
      (ampE n (F.wit n) (F.anc n)
        (n + (F.wit n + (F.anc n + 1))) hoff)) :
    ShiTMCopyStageWithSkip.copyBytes 1 F n =
      (ShiBQP.encCirc
        (ShiEmbed.embedCirc
          (ampE n (F.wit n) (F.anc n)
            (n + (F.wit n + (F.anc n + 1))) hoff)
          he (F.circ n))).map bit := by
  simpa [ShiTMCopyStageWithSkip.copyBytes,
    ShiTMPieceController.expectedPieces] using
      congrArg (List.map bit)
        (encode_copy1_local_eq_embedCirc
          n (F.wit n) (F.anc n) hoff he (F.circ n))

/-- The third pass uses the local table for the last embedded copy. -/
theorem copy2Bytes_eq_embedCirc (F : ShiClassQMA.QMAFamily) (n : Nat)
    (hoff : 2 * (n + (F.wit n + (F.anc n + 1))) +
      (n + (F.wit n + (F.anc n + 1))) ≤
      3 * (n + (F.wit n + (F.anc n + 1))))
    (he : Function.Injective
      (ampE n (F.wit n) (F.anc n)
        (2 * (n + (F.wit n + (F.anc n + 1)))) hoff)) :
    ShiTMCopyStageWithSkip.copyBytes 2 F n =
      (ShiBQP.encCirc
        (ShiEmbed.embedCirc
          (ampE n (F.wit n) (F.anc n)
            (2 * (n + (F.wit n + (F.anc n + 1)))) hoff)
          he (F.circ n))).map bit := by
  simpa [ShiTMCopyStageWithSkip.copyBytes,
    ShiTMPieceController.expectedPieces] using
      congrArg (List.map bit)
        (encode_copy2_local_eq_embedCirc
          n (F.wit n) (F.anc n) hoff he (F.circ n))

end ShiTMCompleteController
