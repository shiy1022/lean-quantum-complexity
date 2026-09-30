import «AMPUNI-copy-local-blocks»
import «AMPUNI-raw-layout-contract»

set_option autoImplicit false

open ShiShallow ShiClassQMAAmp

namespace ShiTMRawLayout

/-- The existing five-gate encoding contract needs only an index-map identity; its piece
table need not be the global thirteen-piece table when source indices are copy-local. -/
theorem encode_local_mapOperands_eq_embedInstr
    (D : List (Nat × Nat) → Nat → Nat) (ps : List (Nat × Nat))
    (n wit anc off : Nat)
    (hoff : off + (n + (wit + (anc + 1))) ≤ 3 * (n + (wit + (anc + 1))))
    (he : Function.Injective (ampE n wit anc off hoff))
    (hmap : ∀ i : Fin (n + (wit + (anc + 1))),
      D ps i.val = ((ampE n wit anc off hoff) i).val)
    (g : Instr (n + (wit + (anc + 1)))) :
    encode (mapOperands D ps 0 (ofInstr g)) =
      ShiBQP.encInstr (ShiEmbed.embedInstr (ampE n wit anc off hoff) he g) := by
  have hc := ShiTM.encInstr_of_embedInstr_tag_preserved_index_remapped.1
    (n + (wit + (anc + 1)))
    (n + (3 * wit + ((2 * n + 3 * anc + 3) + 1)))
    (ampE n wit anc off hoff) he
  cases g with
  | h i => simp only [ofInstr, mapOperands, encode, hc.1, Nat.zero_add, hmap]
  | s i => simp only [ofInstr, mapOperands, encode, hc.2.1, Nat.zero_add, hmap]
  | t i => simp only [ofInstr, mapOperands, encode, hc.2.2.1, Nat.zero_add, hmap]
  | x i => simp only [ofInstr, mapOperands, encode, hc.2.2.2.1, Nat.zero_add, hmap]
  | cnot i j hij =>
      simp only [ofInstr, mapOperands, encode, hc.2.2.2.2.1, Nat.zero_add, hmap]

/-- The same local contract lifts through layer and circuit length prefixes. -/
theorem encode_local_mapCirc_eq_embedCirc
    (D : List (Nat × Nat) → Nat → Nat) (ps : List (Nat × Nat))
    (n wit anc off : Nat)
    (hoff : off + (n + (wit + (anc + 1))) ≤ 3 * (n + (wit + (anc + 1))))
    (he : Function.Injective (ampE n wit anc off hoff))
    (hmap : ∀ i : Fin (n + (wit + (anc + 1))),
      D ps i.val = ((ampE n wit anc off hoff) i).val)
    (c : Layered (n + (wit + (anc + 1)))) :
    encodeCirc (mapCirc D ps 0 (c.map (List.map ofInstr))) =
      ShiBQP.encCirc (ShiEmbed.embedCirc (ampE n wit anc off hoff) he c) := by
  have hLayer (l : List (Instr (n + (wit + (anc + 1))))) :
      encodeLayer (mapLayer D ps 0 (l.map ofInstr)) =
        ShiBQP.encLayer (ShiEmbed.embedLayer (ampE n wit anc off hoff) he l) := by
    have hGate :
        l.map (fun g => encode (mapOperands D ps 0 (ofInstr g))) =
          l.map (fun g => ShiBQP.encInstr
            (ShiEmbed.embedInstr (ampE n wit anc off hoff) he g)) := by
      apply List.map_congr_left
      intro g _
      exact encode_local_mapOperands_eq_embedInstr D ps n wit anc off hoff he hmap g
    unfold encodeLayer mapLayer ShiBQP.encLayer ShiBQP.encStr ShiEmbed.embedLayer
    simp only [List.length_map, List.map_map]
    simpa only [Function.comp_def] using
      congrArg (fun xs : List (List Bool) => ShiBQP.encNat l.length ++ xs.flatten) hGate
  have hLayers :
      c.map (fun l => encodeLayer (mapLayer D ps 0 (l.map ofInstr))) =
        c.map (fun l => ShiBQP.encLayer
          (ShiEmbed.embedLayer (ampE n wit anc off hoff) he l)) := by
    apply List.map_congr_left
    intro l _
    exact hLayer l
  unfold encodeCirc mapCirc ShiBQP.encCirc ShiBQP.encStr ShiEmbed.embedCirc
  simp only [List.length_map, List.map_map]
  simpa only [Function.comp_def] using
    congrArg (fun xs : List (List Bool) => ShiBQP.encNat c.length ++ xs.flatten) hLayers

end ShiTMRawLayout
