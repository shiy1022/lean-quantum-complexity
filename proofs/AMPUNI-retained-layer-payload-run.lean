import «AMPUNI-retained-payload-run»

set_option autoImplicit false
set_option maxHeartbeats 2000000
open ShiShallow Turing Turing.TM2
namespace ShiTMRetainedPayload
open ShiTMLayoutMachine ShiTMOuterLift ShiTMRetainedTop

/-- The global prefix already consumed the circuit depth header and loaded
its counter. Start directly at the layer loop while framing retained data. -/
theorem typed_layers_run_zero (ps : List (Nat × Nat)) {m : Nat}
    (hfit : m ≤ (ps.map Prod.fst).sum) (c : Layered m)
    (rest : List Cell) (pa ta pb tb : List Cell) (v : Sig)
    (S : ∀ k, List (Gam k)) (C : Fin 2 → List Cell)
    (H : Fin 4 → List Cell)
    (hSsrc : S 11 = (ShiTMCircuitNormalization.stripCircPrefix c).map bit ++ rest)
    (hC0 : C 0 = List.replicate c.length Cell.mark) (hC1 : C 1 = [])
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
      run^[layerListCost pa pb
        (typedLayers ps 0 (by simpa using hfit) c)]
        (some { l := some (some (.inr .layerDriver)), var := v, stk := topStacks (liftStacks S C) H }) =
          some { l := some (some (.inr .exit)), var := none, stk := topStacks (liftStacks U D) H }
      ∧ D 0 = [] ∧ D 1 = []
      ∧ U 13 = ((((ShiTMRawLayout.mapCirc depth ps 0
            (c.map (List.map ShiTMRawLayout.ofInstr))).map
              ShiTMRawLayout.encodeLayer).flatten).map bit).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  let layers := typedLayers ps 0 (by simpa using hfit) c
  have hs : S 11 = sourceLayers layers ++ rest := by
    have he : sourceLayers layers = ((c.map ShiBQP.encLayer).flatten).map bit :=
      sourceLayers_typed_zero ps hfit c
    rw [he]
    simpa only [ShiTMCircuitNormalization.stripCircPrefix_eq_payload,
      ShiTMCircuitNormalization.payload] using hSsrc
  have hc : C 0 = List.replicate layers.length Cell.mark := by
    simpa [layers, typedLayers] using hC0
  obtain ⟨U, D, hr, hD0, hD1, hacc, h6, h7, h11, h12,
      h0, h1, h2, h3, h4, h8, h9, h10⟩ :=
    nested_circuit_layers ps layers rest pa ta pb tb v S C
      hs hc hC1 hS0 hS1 hS2 hS3 hS4 hS6 hS7 hS8 hS9 hS10 hS12
      hpa hpb hpaGood hpbGood
  have hp := ShiTMPayload.run_iter_lift (layerListCost pa pb layers)
    (some ⟨some (.inr .layerDriver), v, liftStacks S C⟩)
  rw [hr] at hp
  simp only [Option.map_some, ShiTMPayload.liftCfg, Option.map_some] at hp
  have ht := ShiTMTopFrame.run_iter_frame ShiTMPayload.machine H
    (layerListCost pa pb layers)
    (some ⟨some (some (.inr .layerDriver)), v, liftStacks S C⟩)
  change run^[_] _ = (ShiTMPayload.run^[_] _).map (ShiTMTopFrame.cfg H) at ht
  rw [hp] at ht
  refine ⟨U, D, ht, hD0, hD1, ?_, h6, h7, h11, h12,
    h0, h1, h2, h3, h4, h8, h9, h10⟩
  rw [hacc]
  exact congrArg (fun xs : List Cell => xs.reverse ++ S 13)
    (targetLayers_typed ps 0 (by simpa using hfit) c)

end ShiTMRetainedPayload
