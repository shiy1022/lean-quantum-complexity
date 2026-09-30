import «AMPUNI-loop-typed»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open ShiShallow Turing Turing.TM2

namespace ShiTMLayoutMachine

theorem typedRecord_source_zero (ps : List (Nat × Nat)) {m : Nat}
    (hfit : m ≤ (ps.map Prod.fst).sum) (g : Instr m) :
    (typedRecord ps 0 (by simpa using hfit) g).source =
      (ShiBQP.encInstr g).map bit := by
  have hraw : ShiTMRawLayout.mapOperands (fun _ x => x) ps 0
      (ShiTMRawLayout.ofInstr g) = ShiTMRawLayout.ofInstr g := by
    cases g <;> simp [ShiTMRawLayout.mapOperands, ShiTMRawLayout.ofInstr]
  rw [typedRecord_source, hraw, ShiTMRawLayout.encode_ofInstr]

theorem typedRecord_sourceList_zero (ps : List (Nat × Nat)) {m : Nat}
    (hfit : m ≤ (ps.map Prod.fst).sum) (gs : List (Instr m)) :
    SourceRecord.sourceList
      (gs.map (typedRecord ps 0 (by simpa using hfit))) =
        ((gs.map ShiBQP.encInstr).flatten).map bit := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, SourceRecord.sourceList, List.flatten_cons, List.map_append]
    rw [typedRecord_source_zero ps hfit g, ih]

/-- The unshifted typed gate stream runs through the concrete instruction loop. -/
theorem loop_typed_gate_stream_zero
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
      ∧ U 13 = (SourceRecord.targetList
          (gs.map (typedRecord ps 0 (by simpa using hfit)))).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  apply loop_records ps (gs.map (typedRecord ps 0 (by simpa using hfit))) rest
    pa ta pb tb v S
  · rw [typedRecord_sourceList_zero ps hfit gs]
    exact hSsrc
  all_goals assumption

end ShiTMLayoutMachine
