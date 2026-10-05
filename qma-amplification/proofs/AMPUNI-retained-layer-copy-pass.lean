import «AMPUNI-copy-stage-with-skip-layout-ready»
import «AMPUNI-retained-layer-payload-run»
import «AMPUNI-output-entry-stack-split»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open ShiShallow Turing Turing.TM2

namespace ShiTMRetainedPayload

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOuterLift
  ShiTMPieceController ShiTMOutputEntry

/-- Exact parser cost for a local verifier copy. -/
noncomputable def layerCopyCost (copy : Fin 3) (F : ShiClassQMA.QMAFamily) (n : Nat) : Nat :=
  let ps := expectedPieces copy n (F.wit n) (F.anc n)
  layerListCost
    (pieceCells Prod.fst ps).reverse (pieceCells Prod.snd ps).reverse
    (typedLayers ps 0 (by simp [ps, expectedPieces_width]) (F.circ n))

/-- One copy-specific circuit pass starts from the state produced by the
local table and mirror initialization, with the depth counter already loaded. It prepends the circuit payload to
the reversed output accumulator, consumes the source, and leaves all retained
headers unchanged for the next replay. -/
theorem layer_copy_pass_from_ready (copy : Fin 3)
    (F : ShiClassQMA.QMAFamily) (n : Nat)
    (P : ∀ j, List (TopGam j))
    (hsrc : P ShiTMReplayReload.source =
      (ShiTMCircuitNormalization.stripCircPrefix (F.circ n)).map bit)
    (h0 : P (.inl (.inl (0 : Fin 14))) = [])
    (h1 : P (.inl (.inl (1 : Fin 14))) =
      pieceCells Prod.fst (expectedPieces copy n (F.wit n) (F.anc n)))
    (h2 : P (.inl (.inl (2 : Fin 14))) =
      pieceCells Prod.snd (expectedPieces copy n (F.wit n) (F.anc n)))
    (h3 : P (.inl (.inl (3 : Fin 14))) = [])
    (h4 : P (.inl (.inl (4 : Fin 14))) = [Cell.delim])
    (h6 : P (.inl (.inl (6 : Fin 14))) = [])
    (h7 : P (.inl (.inl (7 : Fin 14))) = [])
    (h8 : P (.inl (.inl (8 : Fin 14))) =
      (pieceCells Prod.fst
        (expectedPieces copy n (F.wit n) (F.anc n))).reverse ++
        [Cell.mirrorEnd])
    (h9 : P (.inl (.inl (9 : Fin 14))) =
      (pieceCells Prod.snd
        (expectedPieces copy n (F.wit n) (F.anc n))).reverse ++
        [Cell.mirrorEnd])
    (h10 : P (.inl (.inl (10 : Fin 14))) = [])
    (h12 : P (.inl (.inl (12 : Fin 14))) = [])
    (hc0 : P (.inl (.inr (0 : Fin 2))) = List.replicate (F.circ n).length Cell.mark)
    (hc1 : P (.inl (.inr (1 : Fin 2))) = []) :
    ∃ (Q : ∀ j, List (TopGam j)) (steps : Nat),
      run^[steps]
        (some ⟨some (some (.inr .layerDriver)), none, P⟩) =
        some ⟨some (some (.inr .exit)), none, Q⟩
      ∧ Q (.inl (.inl (13 : Fin 14))) =
          ((((ShiTMRawLayout.mapCirc depth
              (expectedPieces copy n (F.wit n) (F.anc n)) 0
              ((F.circ n).map (List.map ShiTMRawLayout.ofInstr))).map
                ShiTMRawLayout.encodeLayer).flatten).map bit).reverse ++
            P (.inl (.inl (13 : Fin 14)))
      ∧ Q ShiTMReplayReload.source = []
      ∧ Q (.inl (.inl (0 : Fin 14))) = []
      ∧ Q (.inl (.inl (3 : Fin 14))) = []
      ∧ Q (.inl (.inl (10 : Fin 14))) = []
      ∧ Q (.inl (.inl (4 : Fin 14))) = [Cell.delim]
      ∧ Q (.inl (.inl (6 : Fin 14))) = []
      ∧ Q (.inl (.inl (7 : Fin 14))) = []
      ∧ Q (.inl (.inl (12 : Fin 14))) = []
      ∧ Q (.inl (.inr (0 : Fin 2))) = []
      ∧ Q (.inl (.inr (1 : Fin 2))) = []
      ∧ (∀ j : Fin 4, Q (.inr j) = P (.inr j))
      ∧ steps = layerCopyCost copy F n := by
  let ps := expectedPieces copy n (F.wit n) (F.anc n)
  let pa := (pieceCells Prod.fst ps).reverse
  let pb := (pieceCells Prod.snd ps).reverse
  let B := ShiTMOutputEntry.baseStacks P
  let C := ShiTMOutputEntry.counterStacks P
  let H := ShiTMOutputEntry.headerStacks P
  have hfit : n + (F.wit n + (F.anc n + 1)) ≤
      (ps.map Prod.fst).sum := by
    simpa [ps, expectedPieces_width]
  have hB11 : B 11 = (ShiTMCircuitNormalization.stripCircPrefix (F.circ n)).map bit ++ [] := by
    simpa [B, ShiTMOutputEntry.baseStacks] using hsrc
  have hC0 : C 0 = List.replicate (F.circ n).length Cell.mark := by
    simpa [C, ShiTMOutputEntry.counterStacks] using hc0
  have hC1 : C 1 = [] := by
    simpa [C, ShiTMOutputEntry.counterStacks] using hc1
  have hB0 : B 0 = [] := by
    simpa [B, ShiTMOutputEntry.baseStacks] using h0
  have hB1 : B 1 = pieceCells Prod.fst ps := by
    simpa [B, ShiTMOutputEntry.baseStacks, ps] using h1
  have hB2 : B 2 = pieceCells Prod.snd ps := by
    simpa [B, ShiTMOutputEntry.baseStacks, ps] using h2
  have hB3 : B 3 = [] := by
    simpa [B, ShiTMOutputEntry.baseStacks] using h3
  have hB4 : B 4 = [Cell.delim] := by
    simpa [B, ShiTMOutputEntry.baseStacks] using h4
  have hB6 : B 6 = [] := by
    simpa [B, ShiTMOutputEntry.baseStacks] using h6
  have hB7 : B 7 = [] := by
    simpa [B, ShiTMOutputEntry.baseStacks] using h7
  have hB8 : B 8 = pa ++ Cell.mirrorEnd :: [] := by
    simpa [B, ShiTMOutputEntry.baseStacks, pa, ps] using h8
  have hB9 : B 9 = pb ++ Cell.mirrorEnd :: [] := by
    simpa [B, ShiTMOutputEntry.baseStacks, pb, ps] using h9
  have hB10 : B 10 = [] := by
    simpa [B, ShiTMOutputEntry.baseStacks] using h10
  have hB12 : B 12 = [] := by
    simpa [B, ShiTMOutputEntry.baseStacks] using h12
  have hpa : pa.reverse = pieceCells Prod.fst ps := by simp [pa]
  have hpb : pb.reverse = pieceCells Prod.snd ps := by simp [pb]
  have hpaGood : ∀ y ∈ pa, y ≠ Cell.mirrorEnd := by
    intro y hy
    exact pieceCells_ne_mirrorEnd Prod.fst ps y (by simpa [pa] using hy)
  have hpbGood : ∀ y ∈ pb, y ≠ Cell.mirrorEnd := by
    intro y hy
    exact pieceCells_ne_mirrorEnd Prod.snd ps y (by simpa [pb] using hy)
  obtain ⟨B', D, hpass, hD0, hD1, hacc, hB6', hB7', h11, hB12',
    hB0', _, _, hB3', hB4', _, _, hB10'⟩ :=
    typed_layers_run_zero ps hfit (F.circ n)
      [] pa [] pb [] none B C H
      hB11 hC0 hC1 hB0 hB1 hB2 hB3 hB4 hB6 hB7
      hB8 hB9 hB10 hB12 hpa hpb hpaGood hpbGood
  let Q := topStacks (liftStacks B' D) H
  have hsplit : topStacks (liftStacks B C) H = P := stack_split P
  have hpass' : run^[layerListCost pa pb
        (typedLayers ps 0 (by simpa using hfit) (F.circ n))]
      (some ⟨some (some (.inr .layerDriver)), none, P⟩) =
        some ⟨some (some (.inr .exit)), none, Q⟩ := by
    simpa [Q, hsplit, Nat.add_assoc] using hpass
  refine ⟨Q,
    layerListCost pa pb
      (typedLayers ps 0 (by simpa using hfit) (F.circ n)),
    hpass', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change B' 13 = _
    rw [hacc]
    rfl
  · change B' 11 = []
    exact h11
  · change B' 0 = []
    exact hB0'
  · change B' 3 = []
    exact hB3'
  · change B' 10 = []
    exact hB10'
  · change B' 4 = [Cell.delim]
    exact hB4'
  · change B' 6 = []
    exact hB6'
  · change B' 7 = []
    exact hB7'
  · change B' 12 = []
    exact hB12'
  · change D 0 = []
    exact hD0
  · change D 1 = []
    exact hD1
  · intro j
    rfl
  · rfl

end ShiTMRetainedPayload
