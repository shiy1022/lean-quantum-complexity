import «AMPUNI-complete-controller-forward-output»
import «AMPUNI-concrete-copy-alignment»

set_option autoImplicit false

open ShiShallow

namespace ShiTMCompleteController

open ShiTMLayoutMachine

private theorem bit_injective : Function.Injective bit := by
  intro x y h
  cases x <;> cases y <;> simp [bit] at h ⊢

/-- The forward bit string emitted by the three-pass controller has the exact
three embedded verifier-copy circuit encodings, not merely extensionally
equivalent local-layout encodings. -/
theorem intermediateBits_exact_copies
    (F : ShiClassQMA.QMAFamily) (n : Nat) :
    intermediateBits F n =
      ShiBQP.encNat (3 * F.wit n) ++
      ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
      ShiBQP.encNat (3 * n + 3 * F.wit n + 3 * F.anc n + 3) ++
      ShiBQP.encCirc (embeddedCopy0 F n) ++
      ShiBQP.encCirc (embeddedCopy1 F n) ++
      ShiBQP.encCirc (embeddedCopy2 F n) := by
  have hm : Function.Injective (List.map bit) :=
    List.map_injective_iff.mpr bit_injective
  have e0 :
      ShiTMRawLayout.encodeCirc
        (ShiTMRawLayout.mapCirc depth
          (ShiTMRawLayout.ampPieces n (F.wit n) (F.anc n)) 0
          ((F.circ n).map (List.map ShiTMRawLayout.ofInstr))) =
        ShiBQP.encCirc (embeddedCopy0 F n) := by
    apply hm
    exact firstCopyBytes_eq_exact_copy F n
  have e1 :
      ShiTMRawLayout.encodeCirc
        (ShiTMRawLayout.mapCirc depth
          (ShiTMPieceController.expectedPieces 1 n (F.wit n) (F.anc n)) 0
          ((F.circ n).map (List.map ShiTMRawLayout.ofInstr))) =
        ShiBQP.encCirc (embeddedCopy1 F n) := by
    apply hm
    exact copy1Bytes_eq_exact_copy F n
  have e2 :
      ShiTMRawLayout.encodeCirc
        (ShiTMRawLayout.mapCirc depth
          (ShiTMPieceController.expectedPieces 2 n (F.wit n) (F.anc n)) 0
          ((F.circ n).map (List.map ShiTMRawLayout.ofInstr))) =
        ShiBQP.encCirc (embeddedCopy2 F n) := by
    apply hm
    exact copy2Bytes_eq_exact_copy F n
  unfold intermediateBits
  rw [e0, e1, e2]

end ShiTMCompleteController
