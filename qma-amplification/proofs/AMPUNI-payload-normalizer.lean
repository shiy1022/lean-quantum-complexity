import «AMPUNI-nested-circuit-layers»
import «AMPUNI-payload-machine»
import «AMPUNI-nested-typed-circuit-bridge»
import «AMPUNI-copy-local-embed»
import «AMPUNI-circuit-normalization-spec»
import «AMPUNI-retained-finite»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMPayload

open ShiTMLayoutMachine ShiTMOuterLift

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- A concrete machine consumes one encoded circuit and emits only its translated
layer payload. It strips the local depth prefix while preserving every layer
header, source suffix, and layout/archive frame. -/
theorem payload_circuit_run (ps : List (Nat × Nat))
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
      run^[(layers.length + 1) + layerListCost pa pb layers]
        (some { l := some none, var := v, stk := liftStacks S C }) =
          some { l := some (some (.inr .exit)), var := none, stk := liftStacks U D }
      ∧ D 0 = [] ∧ D 1 = []
      ∧ U 13 = (targetLayers layers).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  let O := liftStacks S C
  obtain ⟨H, hheader, hH11, hHc, hHframe⟩ :=
    strip_header_run layers.length (sourceLayers layers ++ rest) v O
      (by simpa [O, liftStacks, List.append_assoc] using hSsrc)
  let B := baseStacks H
  let C' := counterStacks H
  have hsplit : liftStacks B C' = H := liftStacks_split H
  have hB11 : B 11 = sourceLayers layers ++ rest := hH11
  have hC'0 : C' 0 = List.replicate layers.length Cell.mark := by
    simpa [C', counterStacks, O, liftStacks, hC0] using hHc
  have hC'1 : C' 1 = [] := by
    simpa [C', counterStacks, O, liftStacks] using
      (hHframe (.inr (1 : Fin 2)) (by simp) (by decide)).trans hC1
  have hB13 : B 13 = S 13 := by
    simpa [B, baseStacks, O, liftStacks] using
      hHframe (.inl (13 : Fin 14)) (by decide) (by simp)
  have hBkeep : ∀ k : Fin 14, k ≠ 11 → k ≠ 13 → B k = S k := by
    intro k hk11 hk13
    have h11 : (Sum.inl k : OuterK) ≠ .inl (11 : Fin 14) := by simpa using hk11
    simpa [B, baseStacks, O, liftStacks] using hHframe (.inl k) h11 (by simp)
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
  · have hheader' : run^[layers.length + 1]
        (some { l := some none, var := v, stk := liftStacks S C }) =
          some { l := some (some (.inr .layerDriver)), var := some Cell.delim, stk := liftStacks B C' } := by
      simpa [O, hsplit] using hheader
    have hbody := run_iter_lift (layerListCost pa pb layers)
      (some ⟨some (.inr .layerDriver), some Cell.delim, liftStacks B C'⟩)
    rw [hlayers] at hbody
    exact iterTwo run (layers.length + 1) (layerListCost pa pb layers)
      _ _ _ hheader' (by simpa [liftCfg] using hbody)
  · rw [hacc, hB13]
  · rw [h8, hBkeep 8 (by decide) (by decide)]
  · rw [h9, hBkeep 9 (by decide) (by decide)]

end ShiTMPayload

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open ShiShallow Turing Turing.TM2

namespace ShiTMPayload

open ShiTMLayoutMachine ShiTMOuterLift

/-- The header-stripping machine emits precisely the translated layer payload
of a typed verifier circuit, with no local circuit-depth prefix. -/
theorem payload_typed_circuit_run_zero (ps : List (Nat × Nat)) {m : Nat}
    (hfit : m ≤ (ps.map Prod.fst).sum) (c : Layered m)
    (rest : List Cell) (pa ta pb tb : List Cell) (v : Sig)
    (S : ∀ k, List (Gam k)) (C : Fin 2 → List Cell)
    (hSsrc : S 11 = (ShiBQP.encCirc c).map bit ++ rest)
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
      run^[(c.length + 1) + layerListCost pa pb
        (typedLayers ps 0 (by simpa using hfit) c)]
        (some { l := some none, var := v, stk := liftStacks S C }) =
          some { l := some (some (.inr .exit)), var := none, stk := liftStacks U D }
      ∧ D 0 = [] ∧ D 1 = []
      ∧ U 13 = ((((ShiTMRawLayout.mapCirc depth ps 0
            (c.map (List.map ShiTMRawLayout.ofInstr))).map
              ShiTMRawLayout.encodeLayer).flatten).map bit).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  let layers := typedLayers ps 0 (by simpa using hfit) c
  have hsrc : S 11 = (ShiBQP.encNat layers.length).map bit ++
      sourceLayers layers ++ rest := by
    rw [show layers.length = c.length by simp [layers, typedLayers]]
    rw [sourceCircuit_typed_zero ps hfit c]
    exact hSsrc
  obtain ⟨U, D, hrun, hD0, hD1, hacc, h6, h7, h11, h12,
    h0, h1, h2, h3, h4, h8, h9, h10⟩ :=
    payload_circuit_run ps layers rest pa ta pb tb v S C
      hsrc hC0 hC1 hS0 hS1 hS2 hS3 hS4 hS6 hS7
      hS8 hS9 hS10 hS12 hpa hpb hpaGood hpbGood
  refine ⟨U, D, ?_, hD0, hD1, ?_, h6, h7, h11, h12,
    h0, h1, h2, h3, h4, h8, h9, h10⟩
  · simpa [layers, typedLayers] using hrun
  · rw [hacc]
    have hout := targetLayers_typed ps 0 (by simpa using hfit) c
    simpa [layers, typedLayers, List.length_map] using
      congrArg (fun xs : List Cell => xs.reverse ++ S 13) hout

end ShiTMPayload

set_option autoImplicit false

open ShiShallow Turing Turing.TM2

namespace ShiTMPayload

open ShiTMLayoutMachine ShiTMOuterLift

/-- This is a finite control machine. The layout tables are supplied on its
working stacks; this bundle alone is not a Boolean-I/O uniformity theorem. -/
def finiteMachine : Turing.FinTM2 where
  K := OuterK
  kDecidableEq := inferInstance
  kFin := inferInstance
  k₀ := .inl (11 : Fin 14)
  k₁ := .inl (13 : Fin 14)
  Γ := OuterGam
  Λ := PayloadLabel
  main := none
  ΛFin := inferInstance
  σ := Sig
  initialState := none
  σFin := inferInstance
  Γk₀Fin := inferInstance
  m := machine

/-- Equality of complete, equally deep circuit encodings implies equality of
payloads. This connects the payload machine to the final normalizer contract. -/
theorem raw_payload_eq_strip {N : Nat}
    (raw : List (List ShiTMRawLayout.RawInstr)) (c : Layered N)
    (hlen : raw.length = c.length)
    (henc : ShiTMRawLayout.encodeCirc raw = ShiBQP.encCirc c) :
    (raw.map ShiTMRawLayout.encodeLayer).flatten =
      ShiTMCircuitNormalization.stripCircPrefix c := by
  rw [ShiTMCircuitNormalization.stripCircPrefix_eq_payload]
  unfold ShiTMRawLayout.encodeCirc ShiBQP.encCirc ShiBQP.encStr at henc
  simp only [List.length_map, hlen] at henc
  exact List.append_cancel_left henc

/-- All three copy layouts use the same machine; its raw emitted payload is
exactly the typed embedded circuit payload, with no extra depth prefix. -/
theorem local_copy_payload_eq_strip
    (ps : List (Nat × Nat)) {m N : Nat} (c : Layered m) (out : Layered N)
    (hlen : out.length = c.length)
    (henc : ShiTMRawLayout.encodeCirc
      (ShiTMRawLayout.mapCirc depth ps 0
        (c.map (List.map ShiTMRawLayout.ofInstr))) = ShiBQP.encCirc out) :
    (((ShiTMRawLayout.mapCirc depth ps 0
        (c.map (List.map ShiTMRawLayout.ofInstr))).map
          ShiTMRawLayout.encodeLayer).flatten).map bit =
      (ShiTMCircuitNormalization.stripCircPrefix out).map bit := by
  apply congrArg (List.map bit)
  apply raw_payload_eq_strip _ out _ henc
  simpa [ShiTMRawLayout.mapCirc] using hlen.symm

/-- Exact final-contract payload for verifier copy 0. -/
theorem copy0_payload_eq_strip (n wit anc : Nat)
    (hoff : 0 + (n + (wit + (anc + 1))) ≤
      3 * (n + (wit + (anc + 1))))
    (he : Function.Injective (ShiClassQMAAmp.ampE n wit anc 0 hoff))
    (c : Layered (n + (wit + (anc + 1)))) :
    (((ShiTMRawLayout.mapCirc depth (copyPieces0 n wit anc) 0
        (c.map (List.map ShiTMRawLayout.ofInstr))).map
          ShiTMRawLayout.encodeLayer).flatten).map bit =
      (ShiTMCircuitNormalization.stripCircPrefix
        (ShiEmbed.embedCirc (ShiClassQMAAmp.ampE n wit anc 0 hoff) he c)).map bit := by
  exact local_copy_payload_eq_strip (copyPieces0 n wit anc) c _
    (by simp [ShiEmbed.embedCirc])
    (encode_copy0_local_eq_embedCirc n wit anc hoff he c)

/-- Exact final-contract payload for verifier copy 1. -/
theorem copy1_payload_eq_strip (n wit anc : Nat)
    (hoff : (n + (wit + (anc + 1))) + (n + (wit + (anc + 1))) ≤
      3 * (n + (wit + (anc + 1))))
    (he : Function.Injective (ShiClassQMAAmp.ampE n wit anc (n + (wit + (anc + 1))) hoff))
    (c : Layered (n + (wit + (anc + 1)))) :
    (((ShiTMRawLayout.mapCirc depth (copyPieces1 n wit anc) 0
        (c.map (List.map ShiTMRawLayout.ofInstr))).map
          ShiTMRawLayout.encodeLayer).flatten).map bit =
      (ShiTMCircuitNormalization.stripCircPrefix
        (ShiEmbed.embedCirc (ShiClassQMAAmp.ampE n wit anc (n + (wit + (anc + 1))) hoff) he c)).map bit := by
  exact local_copy_payload_eq_strip (copyPieces1 n wit anc) c _
    (by simp [ShiEmbed.embedCirc])
    (encode_copy1_local_eq_embedCirc n wit anc hoff he c)

/-- Exact final-contract payload for verifier copy 2. -/
theorem copy2_payload_eq_strip (n wit anc : Nat)
    (hoff : (2 * (n + (wit + (anc + 1)))) + (n + (wit + (anc + 1))) ≤
      3 * (n + (wit + (anc + 1))))
    (he : Function.Injective (ShiClassQMAAmp.ampE n wit anc (2 * (n + (wit + (anc + 1)))) hoff))
    (c : Layered (n + (wit + (anc + 1)))) :
    (((ShiTMRawLayout.mapCirc depth (copyPieces2 n wit anc) 0
        (c.map (List.map ShiTMRawLayout.ofInstr))).map
          ShiTMRawLayout.encodeLayer).flatten).map bit =
      (ShiTMCircuitNormalization.stripCircPrefix
        (ShiEmbed.embedCirc (ShiClassQMAAmp.ampE n wit anc (2 * (n + (wit + (anc + 1)))) hoff) he c)).map bit := by
  exact local_copy_payload_eq_strip (copyPieces2 n wit anc) c _
    (by simp [ShiEmbed.embedCirc])
    (encode_copy2_local_eq_embedCirc n wit anc hoff he c)

end ShiTMPayload
