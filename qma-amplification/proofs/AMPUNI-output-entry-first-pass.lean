import «AMPUNI-output-entry-layout-ready»
import «AMPUNI-output-entry-typed-circuit-run»
import «AMPUNI-output-entry-stack-split»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open ShiShallow Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOuterLift ShiTMPieceController

/-- The length-aware entry prefix feeds one full typed verifier-circuit pass.
The output accumulator contains the mapped circuit followed by the amplified
numeric header, both in the machine's reversed-output orientation. -/
theorem entry_then_first_circuit_pass
    (F : ShiClassQMA.QMAFamily) (n : Nat) (v : Sig)
    (S : ∀ j, List (TopGam j))
    (hsrc : S (.inl (.inl (11 : Fin 14))) =
      (ShiBQP.encNat n ++ ShiClassQMAU.encQMAFamilyAt F n).map bit)
    (hret0 : S (.inr (0 : Fin 4)) = [])
    (hret1 : S (.inr (1 : Fin 4)) = [])
    (hret2 : S (.inr (2 : Fin 4)) = [])
    (h13 : S (.inl (.inl (13 : Fin 14))) = [])
    (h3 : S (.inl (.inl (3 : Fin 14))) = [])
    (h1 : S (.inl (.inl (1 : Fin 14))) = [])
    (h2 : S (.inl (.inl (2 : Fin 14))) = [])
    (h8 : S (.inl (.inl (8 : Fin 14))) = [])
    (h9 : S (.inl (.inl (9 : Fin 14))) = [])
    (h10 : S (.inl (.inl (10 : Fin 14))) = [])
    (h0 : S (.inl (.inl (0 : Fin 14))) = [])
    (h4 : S (.inl (.inl (4 : Fin 14))) = [Cell.delim])
    (h6 : S (.inl (.inl (6 : Fin 14))) = [])
    (h7 : S (.inl (.inl (7 : Fin 14))) = [])
    (h12 : S (.inl (.inl (12 : Fin 14))) = [])
    (hc0 : S (.inl (.inr (0 : Fin 2))) = [])
    (hc1 : S (.inl (.inr (1 : Fin 2))) = []) :
    ∃ (U V : ∀ j, List (TopGam j)) (steps : Nat),
      run^[entryCost F n]
        (some { l := some (headerLabel .inputLength), var := v, stk := S }) =
          some { l := some (parserLabel (.inl (.inr .circuitHeader))), var := none, stk := U }
      ∧ run^[steps]
          (some { l := some (parserLabel (.inl (.inr .circuitHeader))), var := none, stk := U }) =
            some { l := some (parserLabel (.inl (.inr .exit))), var := none, stk := V }
      ∧ V (.inl (.inl (13 : Fin 14))) =
          ((ShiTMRawLayout.encodeCirc
              (ShiTMRawLayout.mapCirc depth
                (ShiTMRawLayout.ampPieces n (F.wit n) (F.anc n)) 0
                ((F.circ n).map (List.map ShiTMRawLayout.ofInstr)))).map bit).reverse ++
            ((ShiBQP.encNat (3 * F.wit n) ++
              ShiBQP.encNat (2 * n + 3 * F.anc n + 3) ++
              ShiBQP.encNat
                (3 * n + 3 * F.wit n + 3 * F.anc n + 3)).map bit).reverse
      ∧ V (.inl (.inl (11 : Fin 14))) = []
      ∧ V (.inl (.inl (0 : Fin 14))) = []
      ∧ V (.inl (.inl (3 : Fin 14))) = []
      ∧ V (.inl (.inl (10 : Fin 14))) = []
      ∧ V (.inl (.inl (4 : Fin 14))) = [Cell.delim]
      ∧ V (.inl (.inl (6 : Fin 14))) = []
      ∧ V (.inl (.inl (7 : Fin 14))) = []
      ∧ V (.inl (.inl (12 : Fin 14))) = []
      ∧ V (.inl (.inr (0 : Fin 2))) = []
      ∧ V (.inl (.inr (1 : Fin 2))) = [] := by
  obtain ⟨U, hentry, hU11, hU13, hU1, hU2, _, hU3,
    hU8, hU9, hU10, hU0, hU4, hU6, hU7, hU12, hUC0, hUC1⟩ :=
    full_entry_run F n [] v S (by simpa using hsrc)
      hret0 hret1 hret2 h13 h3 h1 h2 h8 h9 h10
  let ps := ShiTMRawLayout.ampPieces n (F.wit n) (F.anc n)
  let pa := (pieceCells Prod.fst ps).reverse
  let pb := (pieceCells Prod.snd ps).reverse
  let B := baseStacks U
  let C := counterStacks U
  let H := headerStacks U
  have hfit : n + (F.wit n + (F.anc n + 1)) ≤
      (ps.map Prod.fst).sum := by
    exact ampPieces_fit n (F.wit n) (F.anc n)
  have hB11 : B 11 = (ShiBQP.encCirc (F.circ n)).map bit ++ [] := by
    simpa [B, baseStacks] using hU11
  have hC0 : C 0 = [] := by simpa [C, counterStacks, hc0] using hUC0
  have hC1 : C 1 = [] := by simpa [C, counterStacks, hc1] using hUC1
  have hB0 : B 0 = [] := by simpa [B, baseStacks, h0] using hU0
  have hB1 : B 1 = pieceCells Prod.fst ps := by simpa [B, baseStacks, ps] using hU1
  have hB2 : B 2 = pieceCells Prod.snd ps := by simpa [B, baseStacks, ps] using hU2
  have hB3 : B 3 = [] := by simpa [B, baseStacks] using hU3
  have hB4 : B 4 = [Cell.delim] := by simpa [B, baseStacks, h4] using hU4
  have hB6 : B 6 = [] := by simpa [B, baseStacks, h6] using hU6
  have hB7 : B 7 = [] := by simpa [B, baseStacks, h7] using hU7
  have hB8 : B 8 = pa ++ Cell.mirrorEnd :: [] := by
    simpa [B, baseStacks, pa, ps] using hU8
  have hB9 : B 9 = pb ++ Cell.mirrorEnd :: [] := by
    simpa [B, baseStacks, pb, ps] using hU9
  have hB10 : B 10 = [] := by simpa [B, baseStacks] using hU10
  have hB12 : B 12 = [] := by simpa [B, baseStacks, h12] using hU12
  have hpa : pa.reverse = pieceCells Prod.fst ps := by simp [pa]
  have hpb : pb.reverse = pieceCells Prod.snd ps := by simp [pb]
  have hpaGood : ∀ y ∈ pa, y ≠ Cell.mirrorEnd := by
    exact ampPieces_width_mirror_good n (F.wit n) (F.anc n)
  have hpbGood : ∀ y ∈ pb, y ≠ Cell.mirrorEnd := by
    exact ampPieces_base_mirror_good n (F.wit n) (F.anc n)
  obtain ⟨B', D, hpass, hD0, hD1, hacc, h11,
    hB6, hB7, hB12, _, _, hB4, _, _, hB0, hB3, hB10⟩ :=
    typed_circuit_run_zero ps hfit (F.circ n) [] pa [] pb [] none B C H
      hB11 hC0 hC1 hB0 hB1 hB2 hB3 hB4 hB6 hB7
      hB8 hB9 hB10 hB12 hpa hpb hpaGood hpbGood
  let V := topStacks (liftStacks B' D) H
  have hsplit : topStacks (liftStacks B C) H = U := stack_split U
  have hpass' : run^[(F.circ n).length + 1 +
      layerListCost pa pb
        (typedLayers ps 0 (by simpa using hfit) (F.circ n))]
      (some { l := some (parserLabel (.inl (.inr .circuitHeader))), var := none, stk := U }) =
        some { l := some (parserLabel (.inl (.inr .exit))), var := none, stk := V } := by
    simpa [V, hsplit, Nat.add_assoc] using hpass
  refine ⟨U, V,
    (F.circ n).length + 1 + layerListCost pa pb
      (typedLayers ps 0 (by simpa using hfit) (F.circ n)),
    by simpa [parserLabel, bodyLabel, ShiTMOutputStage.stageLabel] using hentry,
    hpass', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change B' 13 = _
    rw [hacc]
    have hB13 : B 13 = U (.inl (.inl (13 : Fin 14))) := rfl
    rw [hB13, hU13]
  · change B' 11 = []
    exact h11
  · change B' 0 = []
    exact hB0
  · change B' 3 = []
    exact hB3
  · change B' 10 = []
    exact hB10
  · change B' 4 = [Cell.delim]
    exact hB4
  · change B' 6 = []
    exact hB6
  · change B' 7 = []
    exact hB7
  · change B' 12 = []
    exact hB12
  · change D 0 = []
    exact hD0
  · change D 1 = []
    exact hD1

end ShiTMOutputEntry
