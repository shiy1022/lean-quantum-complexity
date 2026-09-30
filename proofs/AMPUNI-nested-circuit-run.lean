import «AMPUNI-nested-circuit-layers»
import «AMPUNI-nested-header-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMOuterLift

open ShiTMLayoutMachine

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Complete nested circuit parsing/emission on a valid flat-indexed raw circuit. The
retained verifier's four outer fields and copy-index offsets remain separate obligations. -/
theorem nested_circuit_run (ps : List (Nat × Nat))
    (layers : List (List (SourceRecord ps)))
    (rest : List Cell) (pa ta pb tb : List Cell) (v : Sig)
    (S : ∀ k, List (Gam k)) (C : Fin 2 → List Cell)
    (hSsrc : S 11 = (ShiBQP.encNat layers.length).map bit ++
      sourceLayers layers ++ rest)
    (hC0 : C 0 = []) (hC1 : C 1 = [])
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
      nestedRun^[(layers.length + 1) + layerListCost pa pb layers]
        (some { l := some (.inr .circuitHeader), var := v, stk := liftStacks S C }) =
          some { l := some (.inr .exit), var := none, stk := liftStacks U D }
      ∧ D 0 = [] ∧ D 1 = []
      ∧ U 13 = (((ShiBQP.encNat layers.length).map bit ++
          targetLayers layers).reverse) ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  let O := liftStacks S C
  obtain ⟨H, hheader, hH11, hHc, hH13, hHframe⟩ :=
    nested_header_run 0 layers.length (sourceLayers layers ++ rest) v O
      (by simpa [O, liftStacks, List.append_assoc] using hSsrc)
  let B := baseStacks H
  let C' := counterStacks H
  have hsplit : liftStacks B C' = H := liftStacks_split H
  have hB11 : B 11 = sourceLayers layers ++ rest := hH11
  have hC'0 : C' 0 = List.replicate layers.length Cell.mark := by
    simpa [C', counterStacks, O, liftStacks, hC0] using hHc
  have hC'1 : C' 1 = [] := by
    simpa [C', counterStacks, O, liftStacks] using
      (hHframe (.inr (1 : Fin 2)) (by simp) (by decide) (by simp)).trans hC1
  have hB13 : B 13 = ((ShiBQP.encNat layers.length).map bit).reverse ++ S 13 := by
    simpa [B, baseStacks, O, liftStacks] using hH13
  have hBkeep : ∀ k : Fin 14, k ≠ 11 → k ≠ 13 → B k = S k := by
    intro k hk11 hk13
    have h11 : (Sum.inl k : OuterK) ≠ .inl (11 : Fin 14) := by simpa using hk11
    have h13 : (Sum.inl k : OuterK) ≠ .inl (13 : Fin 14) := by simpa using hk13
    simpa [B, baseStacks, O, liftStacks] using hHframe (.inl k) h11 (by simp) h13
  obtain ⟨U, D, hlayers, hD0, hD1, hacc, h6, h7, h11, h12,
    h0, h1, h2, h3, h4, h8, h9, h10⟩ :=
    nested_circuit_layers ps layers rest pa ta pb tb (some Cell.delim) B C'
      hB11 hC'0 hC'1
      (by rw [hBkeep 0 (by decide) (by decide)]; exact hS0)
      (by rw [hBkeep 1 (by decide) (by decide)]; exact hS1)
      (by rw [hBkeep 2 (by decide) (by decide)]; exact hS2)
      (by rw [hBkeep 3 (by decide) (by decide)]; exact hS3)
      (by rw [hBkeep 4 (by decide) (by decide)]; exact hS4)
      (by rw [hBkeep 6 (by decide) (by decide)]; exact hS6)
      (by rw [hBkeep 7 (by decide) (by decide)]; exact hS7)
      (by rw [hBkeep 8 (by decide) (by decide)]; exact hS8)
      (by rw [hBkeep 9 (by decide) (by decide)]; exact hS9)
      (by rw [hBkeep 10 (by decide) (by decide)]; exact hS10)
      (by rw [hBkeep 12 (by decide) (by decide)]; exact hS12)
      hpa hpb hpaGood hpbGood
  refine ⟨U, D, ?_, hD0, hD1, ?_, h6, h7, h11, h12,
    h0, h1, h2, h3, h4, ?_, ?_, h10⟩
  · have hheader' : nestedRun^[layers.length + 1]
        (some { l := some (.inr .circuitHeader), var := v, stk := liftStacks S C }) =
          some { l := some (.inr .layerDriver), var := some Cell.delim, stk := liftStacks B C' } := by
      simpa [O, hsplit, headerAt, headerNext] using hheader
    exact iterTwo nestedRun (layers.length + 1) (layerListCost pa pb layers)
      _ _ _ hheader' hlayers
  · rw [hacc, hB13]
    simp [List.reverse_append, List.append_assoc]
  · rw [h8, hBkeep 8 (by decide) (by decide)]
  · rw [h9, hBkeep 9 (by decide) (by decide)]

end ShiTMOuterLift
