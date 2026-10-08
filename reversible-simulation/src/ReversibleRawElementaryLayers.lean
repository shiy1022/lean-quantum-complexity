import ReversibleInitializationForestLayers
import ReversibleProgramPayloadBridge

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula

def rawAssignmentLayerCount : RawAssignment → Nat
  | .constant _ b => if b then 1 else 0
  | .copy _ _ => 1
  | .neg _ _ => 2
  | .conj _ _ _ => 37

theorem rawCompile_layerCount {ι : Type} (p : Formula ι) (inputs : ι → Nat) (base : Nat) :
    ((p.rawCompile inputs base).map rawAssignmentLayerCount).sum = formulaElementaryLayers p := by
  induction p generalizing base with
  | constant b => cases b <;> rfl
  | input i => rfl
  | neg p ih =>
    simp [Formula.rawCompile, rawAssignmentLayerCount, formulaElementaryLayers, ih]
  | conj p q ihp ihq =>
    simp [Formula.rawCompile, rawAssignmentLayerCount, formulaElementaryLayers, ihp, ihq, Nat.add_assoc]

theorem falsePadding_layerCount (base count : Nat) :
    ((falsePadding base count).map rawAssignmentLayerCount).sum = 0 := by
  simp [falsePadding, List.map_map, Function.comp_def, rawAssignmentLayerCount]

theorem paddedCompile_layerCount {ι : Type} (p : Formula ι) (inputs : ι → Nat) (base bound : Nat) :
    ((p.paddedCompile inputs base bound).map rawAssignmentLayerCount).sum = formulaElementaryLayers p + 1 := by
  simp [Formula.paddedCompile, rawCompile_layerCount, falsePadding_layerCount, rawAssignmentLayerCount]

theorem paddedForestCompile_layerCount {ι : Type} (ps : List (Formula ι))
    (inputs : ι → Nat) (base bound : Nat) :
    ((paddedForestCompile inputs base bound ps).map rawAssignmentLayerCount).sum =
      (ps.map (fun p => formulaElementaryLayers p + 1)).sum := by
  induction ps generalizing base with
  | nil => rfl
  | cons p ps ih =>
    simp [paddedForestCompile, paddedCompile_layerCount, ih]

theorem rawProgram_reverse_layerCount (nodes : List RawAssignment) :
    (nodes.reverse.map rawAssignmentLayerCount).sum = (nodes.map rawAssignmentLayerCount).sum := by
  simp only [List.map_reverse, List.sum_reverse]

/-- The counted initializer's forest total equals the sum of its actual padded raw-node counts. -/
theorem initializationForestLayerCount_raw (tm : Turing.FinTM2) (e : tm.Γ tm.k₀ ≃ Bool)
    (capacity n : Nat) :
    initializationForestLayerCount tm e capacity n =
      ((paddedForestCompile (fun i : Fin n => i.val) n 17
        (ShiReversibleTM.initialForest tm e capacity n)).map rawAssignmentLayerCount).sum := by
  exact (paddedForestCompile_layerCount _ _ _ _).symm

theorem paddedCompile_distinct_controls {ι : Type} (p : Formula ι) (inputs : ι → Nat) (base bound : Nat) :
    ∀ a ∈ p.paddedCompile inputs base bound, a.DistinctControls := by
  intro a ha
  simp only [Formula.paddedCompile, List.mem_append, List.mem_singleton] at ha
  rcases ha with (ha | ha) | rfl
  · exact rawCompile_distinct_controls p inputs base a ha
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
    trivial
  · trivial

theorem paddedForestCompile_distinct_controls {ι : Type} (ps : List (Formula ι))
    (inputs : ι → Nat) (base bound : Nat) :
    ∀ a ∈ paddedForestCompile inputs base bound ps, a.DistinctControls := by
  induction ps generalizing base with
  | nil => simp [paddedForestCompile]
  | cons p ps ih =>
    intro a ha
    simp only [paddedForestCompile, List.mem_append] at ha
    rcases ha with ha | ha
    · exact paddedCompile_distinct_controls p inputs base bound a ha
    · exact ih (base + (bound + 1)) a ha

end ShiReversibleGenerator
