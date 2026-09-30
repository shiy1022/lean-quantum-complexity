import «AMPUNI-nested-typed-circuit-bridge»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open ShiShallow Turing Turing.TM2

namespace ShiTMOuterLift

open ShiTMLayoutMachine

/-- On an original, unshifted typed circuit encoding, the nested machine emits exactly
the raw mapped-circuit encoding. This is the concrete copy-body interface for `htrans`. -/
theorem nested_typed_circuit_run_zero (ps : List (Nat × Nat)) {m : Nat}
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
      nestedRun^[(c.length + 1) + layerListCost pa pb
        (typedLayers ps 0 (by simpa using hfit) c)]
        (some { l := some (.inr .circuitHeader), var := v, stk := liftStacks S C }) =
          some { l := some (.inr .exit), var := none, stk := liftStacks U D }
      ∧ D 0 = [] ∧ D 1 = []
      ∧ U 13 = ((ShiTMRawLayout.encodeCirc
          (ShiTMRawLayout.mapCirc depth ps 0
            (c.map (List.map ShiTMRawLayout.ofInstr)))).map bit).reverse ++ S 13
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
    nested_circuit_run ps layers rest pa ta pb tb v S C
      hsrc hC0 hC1 hS0 hS1 hS2 hS3 hS4 hS6 hS7
      hS8 hS9 hS10 hS12 hpa hpb hpaGood hpbGood
  refine ⟨U, D, ?_, hD0, hD1, ?_, h6, h7, h11, h12,
    h0, h1, h2, h3, h4, h8, h9, h10⟩
  · simpa [layers, typedLayers] using hrun
  · rw [hacc]
    have hout := targetCircuit_typed ps 0 (by simpa using hfit) c
    simpa [layers, typedLayers, List.length_map] using
      congrArg (fun xs : List Cell => xs.reverse ++ S 13) hout

end ShiTMOuterLift
