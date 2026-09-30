import «AMPUNI-loop-typed-zero»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open ShiShallow Turing Turing.TM2

namespace ShiTMLayoutMachine

/-- The accumulated gate bytes are the body of the existing raw mapped-layer encoding. -/
theorem typedRecord_targetList_eq_mapLayer (ps : List (Nat × Nat))
    (off : Nat) {m : Nat} (hfit : off + m ≤ (ps.map Prod.fst).sum)
    (gs : List (Instr m)) :
    SourceRecord.targetList (gs.map (typedRecord ps off hfit)) =
      ((ShiTMRawLayout.mapLayer depth ps off
        (gs.map ShiTMRawLayout.ofInstr)).map ShiTMRawLayout.encode).flatten.map bit := by
  rw [typedRecord_targetList]
  simp [ShiTMRawLayout.mapLayer, List.map_map, Function.comp_def]

theorem typedRecord_sourceList_zero_eq_layer_body (ps : List (Nat × Nat))
    {m : Nat} (hfit : m ≤ (ps.map Prod.fst).sum)
    (gs : List (Instr m)) :
    SourceRecord.sourceList (gs.map (typedRecord ps 0 (by simpa using hfit))) =
      ((gs.map ShiBQP.encInstr).flatten).map bit :=
  typedRecord_sourceList_zero ps hfit gs

/-- The emitted bytes for the unshifted copy agree with the mapped-layer contract. -/
theorem loop_typed_gate_stream_zero_mapLayer
    (ps : List (Nat × Nat)) {m : Nat}
    (hfit : m ≤ (ps.map Prod.fst).sum) (gs : List (Instr m))
    (rest : List Cell) (pa ta pb tb : List Cell) (v : Sig)
    (S : ∀ k, List (Gam k))
    (hSsrc : S 11 = ((gs.map ShiBQP.encInstr).flatten).map bit ++ rest)
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
    ∃ (vout : Sig) (U : ∀ k, List (Gam k)),
      loopRun^[SourceRecord.loopCost pa pb
        (gs.map (typedRecord ps 0 (by simpa using hfit)))]
        (some { l := some (b .parseTag), var := v, stk := S }) =
          some { l := some (b .parseTag), var := vout, stk := U }
      ∧ U 13 = (((ShiTMRawLayout.mapLayer depth ps 0
          (gs.map ShiTMRawLayout.ofInstr)).map ShiTMRawLayout.encode).flatten.map bit).reverse
          ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  obtain ⟨vout, U, hrun, hacc, h6, h7, h11, h12, h0, h1, h2,
    h3, h4, h8, h9, h10⟩ :=
    loop_typed_gate_stream_zero ps hfit gs rest pa ta pb tb v S
      hSsrc hS0 hS1 hS2 hS3 hS4 hS6 hS7 hS8 hS9 hS10 hS12
      hpa hpb hpaGood hpbGood
  refine ⟨vout, U, hrun, ?_, h6, h7, h11, h12, h0, h1, h2,
    h3, h4, h8, h9, h10⟩
  rw [hacc, typedRecord_targetList_eq_mapLayer]

end ShiTMLayoutMachine
