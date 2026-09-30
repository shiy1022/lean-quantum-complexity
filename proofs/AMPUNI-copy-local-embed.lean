import «AMPUNI-local-embed-contract»

set_option autoImplicit false

open ShiShallow ShiClassQMAAmp

namespace ShiTMLayoutMachine

theorem encode_copy0_local_eq_embedCirc (n wit anc : Nat)
    (hoff : 0 + (n + (wit + (anc + 1))) ≤ 3 * (n + (wit + (anc + 1))))
    (he : Function.Injective (ampE n wit anc 0 hoff))
    (c : Layered (n + (wit + (anc + 1)))) :
    ShiTMRawLayout.encodeCirc
      (ShiTMRawLayout.mapCirc depth (copyPieces0 n wit anc) 0
        (c.map (List.map ShiTMRawLayout.ofInstr))) =
      ShiBQP.encCirc (ShiEmbed.embedCirc (ampE n wit anc 0 hoff) he c) := by
  apply ShiTMRawLayout.encode_local_mapCirc_eq_embedCirc depth
    (copyPieces0 n wit anc) n wit anc 0 hoff he
  intro i
  rw [depth_copy0_global n wit anc i.val i.isLt]
  simpa using depth_ampPieces_eq_ampE n wit anc 0 hoff i

theorem encode_copy1_local_eq_embedCirc (n wit anc : Nat)
    (hoff : (n + (wit + (anc + 1))) + (n + (wit + (anc + 1))) ≤
      3 * (n + (wit + (anc + 1))))
    (he : Function.Injective (ampE n wit anc (n + (wit + (anc + 1))) hoff))
    (c : Layered (n + (wit + (anc + 1)))) :
    ShiTMRawLayout.encodeCirc
      (ShiTMRawLayout.mapCirc depth (copyPieces1 n wit anc) 0
        (c.map (List.map ShiTMRawLayout.ofInstr))) =
      ShiBQP.encCirc
        (ShiEmbed.embedCirc (ampE n wit anc (n + (wit + (anc + 1))) hoff) he c) := by
  apply ShiTMRawLayout.encode_local_mapCirc_eq_embedCirc depth
    (copyPieces1 n wit anc) n wit anc (n + (wit + (anc + 1))) hoff he
  intro i
  rw [depth_copy1_global n wit anc i.val i.isLt]
  exact depth_ampPieces_eq_ampE n wit anc (n + (wit + (anc + 1))) hoff i

theorem encode_copy2_local_eq_embedCirc (n wit anc : Nat)
    (hoff : 2 * (n + (wit + (anc + 1))) + (n + (wit + (anc + 1))) ≤
      3 * (n + (wit + (anc + 1))))
    (he : Function.Injective
      (ampE n wit anc (2 * (n + (wit + (anc + 1)))) hoff))
    (c : Layered (n + (wit + (anc + 1)))) :
    ShiTMRawLayout.encodeCirc
      (ShiTMRawLayout.mapCirc depth (copyPieces2 n wit anc) 0
        (c.map (List.map ShiTMRawLayout.ofInstr))) =
      ShiBQP.encCirc
        (ShiEmbed.embedCirc
          (ampE n wit anc (2 * (n + (wit + (anc + 1)))) hoff) he c) := by
  apply ShiTMRawLayout.encode_local_mapCirc_eq_embedCirc depth
    (copyPieces2 n wit anc) n wit anc (2 * (n + (wit + (anc + 1)))) hoff he
  intro i
  rw [depth_copy2_global n wit anc i.val i.isLt]
  exact depth_ampPieces_eq_ampE n wit anc (2 * (n + (wit + (anc + 1)))) hoff i

end ShiTMLayoutMachine
