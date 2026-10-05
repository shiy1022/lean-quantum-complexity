import «AMPUNI-layout»
import «AMPUNI-layout-data»
import «AMPUNI-raw-layout-contract»

set_option autoImplicit false

open ShiShallow ShiClassQMAAmp

namespace ShiTMLayoutMachine

/-- The concrete layout recursion is the wire map of each amplified copy. -/
theorem depth_ampPieces_eq_ampE
    (n wit anc off : Nat)
    (hoff : off + (n + (wit + (anc + 1))) ≤ 3 * (n + (wit + (anc + 1))))
    (i : Fin (n + (wit + (anc + 1)))) :
    depth (ShiTMRawLayout.ampPieces n wit anc) (off + i.val) =
      ((ampE n wit anc off hoff) i).val := by
  simpa [ShiTMRawLayout.ampPieces] using
    (solution depth (by intro a b r x; rfl) n wit anc off hoff i)

/-- The encoded circuit produced by mapping all copy gates with `depth` is exactly the
corresponding explicit embedded circuit encoding. -/
theorem encode_mapCirc_depth_eq_embedCirc
    (n wit anc off : Nat)
    (hoff : off + (n + (wit + (anc + 1))) ≤ 3 * (n + (wit + (anc + 1))))
    (he : Function.Injective (ampE n wit anc off hoff))
    (c : Layered (n + (wit + (anc + 1)))) :
    ShiTMRawLayout.encodeCirc
      (ShiTMRawLayout.mapCirc depth (ShiTMRawLayout.ampPieces n wit anc) off
        (c.map (List.map ShiTMRawLayout.ofInstr))) =
      ShiBQP.encCirc (ShiEmbed.embedCirc (ampE n wit anc off hoff) he c) := by
  exact ShiTMRawLayout.encode_mapCirc_eq_embedCirc depth n wit anc off hoff he
    (depth_ampPieces_eq_ampE n wit anc off hoff) c

end ShiTMLayoutMachine
