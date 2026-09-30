import «AMPUNI-output-entry-nested-lift»
import «AMPUNI-nested-typed-circuit-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open ShiShallow Turing Turing.TM2

namespace ShiTMOutputEntry

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMOuterLift

/-- One typed circuit pass in the new finite top-level machine is exactly the
previously verified nested pass. The four retained header stacks are framed. -/
theorem typed_circuit_run_zero (ps : List (Nat × Nat)) {m : Nat}
    (hfit : m ≤ (ps.map Prod.fst).sum) (c : Layered m)
    (rest : List Cell) (pa ta pb tb : List Cell) (v : Sig)
    (S : ∀ k, List (Gam k)) (C : Fin 2 → List Cell)
    (H : Fin 4 → List Cell)
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
        (some { l := some (parserLabel (.inl (.inr .circuitHeader))), var := v, stk := topStacks (liftStacks S C) H }) =
          some { l := some (parserLabel (.inl (.inr .exit))), var := none, stk := topStacks (liftStacks U D) H }
      ∧ D 0 = [] ∧ D 1 = []
      ∧ U 13 = ((ShiTMRawLayout.encodeCirc
          (ShiTMRawLayout.mapCirc depth ps 0
            (c.map (List.map ShiTMRawLayout.ofInstr)))).map bit).reverse ++ S 13
      ∧ U 11 = rest
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 12 = []
      ∧ U 1 = pieceCells Prod.fst ps
      ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9
      ∧ U 0 = [] ∧ U 3 = [] ∧ U 10 = [] := by
  obtain ⟨U, D, hrun, hD0, hD1, hacc, h6, h7, h11, h12,
    h0, h1, h2, h3, h4, h8, h9, h10⟩ :=
    nested_typed_circuit_run_zero ps hfit c rest pa ta pb tb v S C
      hSsrc hC0 hC1 hS0 hS1 hS2 hS3 hS4 hS6 hS7
      hS8 hS9 hS10 hS12 hpa hpb hpaGood hpbGood
  refine ⟨U, D, ?_, hD0, hD1, hacc, h11,
    h6, h7, h12, h1, h2, h4, h8, h9, h0, h3, h10⟩
  have hLift := nested_run_lift H
    ((c.length + 1) + layerListCost pa pb
      (typedLayers ps 0 (by simpa using hfit) c))
    (some { l := some (.inr .circuitHeader), var := v, stk := liftStacks S C })
  rw [hrun] at hLift
  simpa [liftNestedCfg, ShiTMRetainedTop.liftCfg, liftCfg, parserLabel] using hLift

end ShiTMOutputEntry
