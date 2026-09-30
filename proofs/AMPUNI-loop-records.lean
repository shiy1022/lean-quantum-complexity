import «AMPUNI-loop-instruction»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMLayoutMachine

def SourceRecord.sourceList {ps : List (Nat × Nat)} : List (SourceRecord ps) → List Cell
  | [] => []
  | r :: rs => r.source ++ sourceList rs

def SourceRecord.targetList {ps : List (Nat × Nat)} : List (SourceRecord ps) → List Cell
  | [] => []
  | r :: rs => r.target ++ targetList rs

noncomputable def SourceRecord.loopCost {ps : List (Nat × Nat)} (pa pb : List Cell) :
    List (SourceRecord ps) → Nat
  | [] => 0
  | r :: rs => r.cost pa pb + 1 + loopCost pa pb rs

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The concrete loop executes any list of well-scoped encoded records and restores
the parser invariant before the next record. -/
theorem loop_records (ps : List (Nat × Nat)) (rs : List (SourceRecord ps))
    (rest : List Cell) (pa ta pb tb : List Cell) (v : Sig)
    (S : ∀ k, List (Gam k))
    (hSsrc : S 11 = SourceRecord.sourceList rs ++ rest)
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
      loopRun^[SourceRecord.loopCost pa pb rs]
        (some { l := some (b .parseTag), var := v, stk := S }) =
          some { l := some (b .parseTag), var := vout, stk := U }
      ∧ U 13 = (SourceRecord.targetList rs).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  induction rs generalizing v S with
  | nil =>
    refine ⟨v, S, rfl, ?_, hS6, hS7, ?_, hS12, hS0, hS1, hS2,
      hS3, hS4, rfl, rfl, hS10⟩
    · rfl
    · simpa [SourceRecord.sourceList] using hSsrc
  | cons r rs ih =>
    have hsrc : S 11 = r.source ++ (SourceRecord.sourceList rs ++ rest) := by
      simpa [SourceRecord.sourceList, List.append_assoc] using hSsrc
    obtain ⟨v1, T, hfirst, hacc, h6, h7, h11, h12, h0, h1, h2,
      h3, h4, h8, h9, h10⟩ :=
      loop_instruction ps r (SourceRecord.sourceList rs ++ rest) pa ta pb tb v S
        hsrc hS0 hS1 hS2 hS3 hS4 hS6 hS7 hS8 hS9 hS10 hS12
        hpa hpb hpaGood hpbGood
    have hrestart : loopRun^[r.cost pa pb + 1]
        (some { l := some (b .parseTag), var := v, stk := S }) =
          some { l := some (b .parseTag), var := v1, stk := T } := by
      exact iterTwo loopRun (r.cost pa pb) 1 _ _ _ hfirst (loopMachine_restart v1 T)
    obtain ⟨vout, U, htail, htailAcc, htail6, htail7, htail11,
      htail12, htail0, htail1, htail2, htail3, htail4,
      htail8, htail9, htail10⟩ :=
      ih v1 T h11 h0 h1 h2 h3 h4 h6 h7
        (by rw [h8]; exact hS8)
        (by rw [h9]; exact hS9) h10 h12
    refine ⟨vout, U, ?_, ?_, htail6, htail7, htail11, htail12,
      htail0, htail1, htail2, htail3, htail4, ?_, ?_, htail10⟩
    · exact iterTwo loopRun (r.cost pa pb + 1) (SourceRecord.loopCost pa pb rs)
        _ _ _ hrestart htail
    · rw [htailAcc, hacc]
      simp [SourceRecord.targetList, List.reverse_append, List.append_assoc]
    · rw [htail8, h8]
    · rw [htail9, h9]

end ShiTMLayoutMachine
