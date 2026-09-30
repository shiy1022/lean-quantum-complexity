import «AMPUNI-nested-layer»
import «AMPUNI-nested-counter-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMOuterLift

open ShiTMLayoutMachine

def sourceLayer {ps : List (Nat × Nat)} (rs : List (SourceRecord ps)) : List Cell :=
  (ShiBQP.encNat rs.length).map bit ++ SourceRecord.sourceList rs

def targetLayer {ps : List (Nat × Nat)} (rs : List (SourceRecord ps)) : List Cell :=
  (ShiBQP.encNat rs.length).map bit ++ SourceRecord.targetList rs

def sourceLayers {ps : List (Nat × Nat)} :
    List (List (SourceRecord ps)) → List Cell
  | [] => []
  | layer :: layers => sourceLayer layer ++ sourceLayers layers

def targetLayers {ps : List (Nat × Nat)} :
    List (List (SourceRecord ps)) → List Cell
  | [] => []
  | layer :: layers => targetLayer layer ++ targetLayers layers

noncomputable def layerListCost {ps : List (Nat × Nat)} (pa pb : List Cell) :
    List (List (SourceRecord ps)) → Nat
  | [] => 1
  | layer :: layers =>
      1 + ((layer.length + 1) + gateListCost pa pb layer) +
        layerListCost pa pb layers

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The outer counter iterates all layers, each of which runs its own counted gate driver. -/
theorem nested_circuit_layers (ps : List (Nat × Nat))
    (layers : List (List (SourceRecord ps)))
    (rest : List Cell) (pa ta pb tb : List Cell) (v : Sig)
    (S : ∀ k, List (Gam k)) (C : Fin 2 → List Cell)
    (hSsrc : S 11 = sourceLayers layers ++ rest)
    (hC0 : C 0 = List.replicate layers.length Cell.mark)
    (hC1 : C 1 = [])
    (hS0 : S 0 = []) (hS1 : S 1 = pieceCells Prod.fst ps)
    (hS2 : S 2 = pieceCells Prod.snd ps) (hS3 : S 3 = [])
    (hS4 : S 4 = [.delim]) (hS6 : S 6 = []) (hS7 : S 7 = [])
    (hS8 : S 8 = pa ++ .mirrorEnd :: ta)
    (hS9 : S 9 = pb ++ .mirrorEnd :: tb) (hS10 : S 10 = [])
    (hS12 : S 12 = [])
    (hpa : pa.reverse = pieceCells Prod.fst ps)
    (hpb : pb.reverse = pieceCells Prod.snd ps)
    (hpaGood : ∀ y ∈ pa, y ≠ .mirrorEnd)
    (hpbGood : ∀ y ∈ pb, y ≠ .mirrorEnd) :
    ∃ (U : ∀ k, List (Gam k)) (D : Fin 2 → List Cell),
      nestedRun^[layerListCost pa pb layers]
        (some { l := some (.inr .layerDriver), var := v, stk := liftStacks S C }) =
          some { l := some (.inr .exit), var := none, stk := liftStacks U D }
      ∧ D 0 = [] ∧ D 1 = []
      ∧ U 13 = (targetLayers layers).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  induction layers generalizing v S C with
  | nil =>
    have hC : C 0 = [] := by simpa using hC0
    refine ⟨S, C, ?_, hC, hC1, ?_, hS6, hS7, ?_, hS12,
      hS0, hS1, hS2, hS3, hS4, rfl, rfl, hS10⟩
    · exact nested_layer_driver_empty v (liftStacks S C) (by simpa [liftStacks] using hC)
    · rfl
    · simpa [sourceLayers] using hSsrc
  | cons layer layers ih =>
    have hsrc : S 11 = (ShiBQP.encNat layer.length).map bit ++
        SourceRecord.sourceList layer ++ (sourceLayers layers ++ rest) := by
      simpa [sourceLayers, sourceLayer, List.append_assoc] using hSsrc
    have hC : C 0 = Cell.mark :: List.replicate layers.length Cell.mark := by
      simpa [List.replicate_succ] using hC0
    let C' := Function.update C 0 (List.replicate layers.length Cell.mark)
    have hpop : nestedRun^[1]
        (some { l := some (.inr .layerDriver), var := v, stk := liftStacks S C }) =
          some { l := some (.inr .layerHeader), var := some Cell.mark, stk := liftStacks S C' } := by
      exact nested_layer_driver_mark_lift v S C _ hC
    have hC'1 : C' 1 = [] := by simpa [C', Function.update_of_ne] using hC1
    obtain ⟨T, D, hlayer, hD1, hD0, hacc, h6, h7, h11, h12,
      h0, h1, h2, h3, h4, h8, h9, h10⟩ :=
      nested_layer ps layer (sourceLayers layers ++ rest) pa ta pb tb
        (some Cell.mark) S C' hsrc hC'1
        hS0 hS1 hS2 hS3 hS4 hS6 hS7 hS8 hS9 hS10 hS12
        hpa hpb hpaGood hpbGood
    have hD0' : D 0 = List.replicate layers.length Cell.mark := by
      rw [hD0]
      simp [C']
    obtain ⟨U, E, htail, hE0, hE1, htailAcc, htail6, htail7,
      htail11, htail12, htail0, htail1, htail2, htail3,
      htail4, htail8, htail9, htail10⟩ :=
      ih none T D h11 hD0' hD1 h0 h1 h2 h3 h4 h6 h7
        (by rw [h8]; exact hS8) (by rw [h9]; exact hS9)
        h10 h12
    have hfirst : nestedRun^[1 + ((layer.length + 1) + gateListCost pa pb layer)]
        (some { l := some (.inr .layerDriver), var := v, stk := liftStacks S C }) =
          some { l := some (.inr .layerDriver), var := none, stk := liftStacks T D } := by
      exact iterTwo nestedRun 1 ((layer.length + 1) + gateListCost pa pb layer)
        _ _ _ hpop hlayer
    refine ⟨U, E, ?_, hE0, hE1, ?_, htail6, htail7, htail11,
      htail12, htail0, htail1, htail2, htail3, htail4, ?_, ?_, htail10⟩
    · exact iterTwo nestedRun
        (1 + ((layer.length + 1) + gateListCost pa pb layer))
        (layerListCost pa pb layers) _ _ _ hfirst htail
    · rw [htailAcc, hacc]
      simp [targetLayers, targetLayer, List.reverse_append, List.append_assoc]
    · rw [htail8, h8]
    · rw [htail9, h9]

end ShiTMOuterLift
