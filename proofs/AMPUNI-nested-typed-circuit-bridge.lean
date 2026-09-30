import «AMPUNI-nested-circuit-run»
import «AMPUNI-loop-typed-zero»
import «AMPUNI-loop-layer-body»
import «AMPUNI-concrete-copy-encoding»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open ShiShallow Turing Turing.TM2

namespace ShiTMOuterLift

open ShiTMLayoutMachine

def typedLayers (ps : List (Nat × Nat)) (off : Nat) {m : Nat}
    (hfit : off + m ≤ (ps.map Prod.fst).sum) (c : Layered m) :
    List (List (SourceRecord ps)) :=
  c.map (fun layer => layer.map (typedRecord ps off hfit))

theorem sourceLayer_typed_zero (ps : List (Nat × Nat)) {m : Nat}
    (hfit : m ≤ (ps.map Prod.fst).sum) (layer : List (Instr m)) :
    sourceLayer (layer.map (typedRecord ps 0 (by simpa using hfit))) =
      (ShiBQP.encLayer layer).map bit := by
  unfold sourceLayer ShiBQP.encLayer ShiBQP.encStr
  rw [List.length_map, typedRecord_sourceList_zero ps hfit layer]
  simp [List.map_append]

theorem targetLayer_typed (ps : List (Nat × Nat)) (off : Nat) {m : Nat}
    (hfit : off + m ≤ (ps.map Prod.fst).sum) (layer : List (Instr m)) :
    targetLayer (layer.map (typedRecord ps off hfit)) =
      (ShiTMRawLayout.encodeLayer
        (ShiTMRawLayout.mapLayer depth ps off
          (layer.map ShiTMRawLayout.ofInstr))).map bit := by
  unfold targetLayer ShiTMRawLayout.encodeLayer
  rw [List.length_map, typedRecord_targetList_eq_mapLayer ps off hfit layer]
  simp [ShiTMRawLayout.mapLayer, List.map_append, List.length_map]

theorem sourceLayers_typed_zero (ps : List (Nat × Nat)) {m : Nat}
    (hfit : m ≤ (ps.map Prod.fst).sum) (c : Layered m) :
    sourceLayers (typedLayers ps 0 (by simpa using hfit) c) =
      ((c.map ShiBQP.encLayer).flatten).map bit := by
  induction c with
  | nil => rfl
  | cons layer c ih =>
    change sourceLayer (layer.map (typedRecord ps 0 (by simpa using hfit))) ++
      sourceLayers (typedLayers ps 0 (by simpa using hfit) c) = _
    rw [sourceLayer_typed_zero ps hfit layer, ih]
    simp [List.map_append]

theorem targetLayers_typed (ps : List (Nat × Nat)) (off : Nat) {m : Nat}
    (hfit : off + m ≤ (ps.map Prod.fst).sum) (c : Layered m) :
    targetLayers (typedLayers ps off hfit c) =
      (((ShiTMRawLayout.mapCirc depth ps off
        (c.map (List.map ShiTMRawLayout.ofInstr))).map
          ShiTMRawLayout.encodeLayer).flatten).map bit := by
  induction c with
  | nil => rfl
  | cons layer c ih =>
    change targetLayer (layer.map (typedRecord ps off hfit)) ++
      targetLayers (typedLayers ps off hfit c) = _
    rw [targetLayer_typed ps off hfit layer, ih]
    simp [ShiTMRawLayout.mapCirc, List.map_append]

theorem sourceCircuit_typed_zero (ps : List (Nat × Nat)) {m : Nat}
    (hfit : m ≤ (ps.map Prod.fst).sum) (c : Layered m) :
    (ShiBQP.encNat c.length).map bit ++
      sourceLayers (typedLayers ps 0 (by simpa using hfit) c) =
        (ShiBQP.encCirc c).map bit := by
  rw [sourceLayers_typed_zero ps hfit c]
  simp [ShiBQP.encCirc, ShiBQP.encStr, List.map_append]

theorem targetCircuit_typed (ps : List (Nat × Nat)) (off : Nat) {m : Nat}
    (hfit : off + m ≤ (ps.map Prod.fst).sum) (c : Layered m) :
    (ShiBQP.encNat c.length).map bit ++
      targetLayers (typedLayers ps off hfit c) =
        (ShiTMRawLayout.encodeCirc
          (ShiTMRawLayout.mapCirc depth ps off
            (c.map (List.map ShiTMRawLayout.ofInstr)))).map bit := by
  rw [targetLayers_typed ps off hfit c]
  simp [ShiTMRawLayout.encodeCirc, ShiTMRawLayout.mapCirc,
    List.map_append, List.length_map]

end ShiTMOuterLift
