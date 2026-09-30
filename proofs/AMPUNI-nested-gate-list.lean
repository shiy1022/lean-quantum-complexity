import «AMPUNI-nested-instruction»
import «AMPUNI-nested-counter-lift»
import «AMPUNI-loop-records»

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

open Turing Turing.TM2

namespace ShiTMOuterLift

open ShiTMLayoutMachine

noncomputable def gateListCost {ps : List (Nat × Nat)} (pa pb : List Cell) :
    List (SourceRecord ps) → Nat
  | [] => 1
  | r :: rs => 1 + r.cost pa pb + 1 + gateListCost pa pb rs

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The inner counter drives every gate in a layer. It exits only after consuming all
`rs.length` marks, preserving the body-level parser invariant and reverse output. -/
theorem nested_gate_list (ps : List (Nat × Nat)) (rs : List (SourceRecord ps))
    (rest : List Cell) (pa ta pb tb : List Cell) (v : Sig)
    (S : ∀ k, List (Gam k)) (C : Fin 2 → List Cell)
    (hSsrc : S 11 = SourceRecord.sourceList rs ++ rest)
    (hcount : C 1 = List.replicate rs.length Cell.mark)
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
      nestedRun^[gateListCost pa pb rs]
        (some { l := some (.inr .gateDriver), var := v, stk := liftStacks S C }) =
          some { l := some (.inr .layerDriver), var := none, stk := liftStacks U D }
      ∧ D 1 = [] ∧ D 0 = C 0
      ∧ U 13 = (SourceRecord.targetList rs).reverse ++ S 13
      ∧ U 6 = [] ∧ U 7 = [] ∧ U 11 = rest ∧ U 12 = []
      ∧ U 0 = [] ∧ U 1 = pieceCells Prod.fst ps ∧ U 2 = pieceCells Prod.snd ps
      ∧ U 3 = [] ∧ U 4 = [.delim]
      ∧ U 8 = S 8 ∧ U 9 = S 9 ∧ U 10 = [] := by
  induction rs generalizing v S C with
  | nil =>
    have hC : C 1 = [] := by simpa using hcount
    refine ⟨S, C, ?_, hC, rfl, ?_, hS6, hS7, ?_, hS12,
      hS0, hS1, hS2, hS3, hS4, rfl, rfl, hS10⟩
    · exact nested_gate_driver_empty v (liftStacks S C) (by simpa [liftStacks] using hC)
    · rfl
    · simpa [SourceRecord.sourceList] using hSsrc
  | cons r rs ih =>
    have hsrc : S 11 = r.source ++ (SourceRecord.sourceList rs ++ rest) := by
      simpa [SourceRecord.sourceList, List.append_assoc] using hSsrc
    have hC : C 1 = Cell.mark :: List.replicate rs.length Cell.mark := by
      simpa [List.replicate_succ] using hcount
    let C' := Function.update C 1 (List.replicate rs.length Cell.mark)
    have hpop : nestedRun^[1]
        (some { l := some (.inr .gateDriver), var := v, stk := liftStacks S C }) =
          some (liftCfg C' { l := some (b .parseTag), var := some Cell.mark, stk := S }) := by
      exact nested_gate_driver_mark_lift v S C _ hC
    obtain ⟨v1, T, hbody, hacc, h6, h7, h11, h12, h0, h1, h2,
      h3, h4, h8, h9, h10⟩ :=
      nested_instruction ps r (SourceRecord.sourceList rs ++ rest) pa ta pb tb
        (some Cell.mark) S C' hsrc hS0 hS1 hS2 hS3 hS4 hS6 hS7
        hS8 hS9 hS10 hS12 hpa hpb hpaGood hpbGood
    have hdone : nestedRun^[1]
        (some (liftCfg C' { l := some (b .instructionDone), var := v1, stk := T })) =
          some { l := some (.inr .gateDriver), var := v1, stk := liftStacks T C' } := by
      exact nested_instruction_done_step v1 (liftStacks T C')
    have hC' : C' 1 = List.replicate rs.length Cell.mark := by simp [C']
    obtain ⟨U, D, htail, hD1, hD0, htailAcc, htail6, htail7,
      htail11, htail12, htail0, htail1, htail2, htail3, htail4,
      htail8, htail9, htail10⟩ :=
      ih v1 T C' h11 hC' h0 h1 h2 h3 h4 h6 h7
        (by rw [h8]; exact hS8) (by rw [h9]; exact hS9)
        h10 h12
    have hfirst : nestedRun^[1 + r.cost pa pb]
        (some { l := some (.inr .gateDriver), var := v, stk := liftStacks S C }) =
          some (liftCfg C' { l := some (b .instructionDone), var := v1, stk := T }) := by
      exact iterTwo nestedRun 1 (r.cost pa pb) _ _ _ hpop hbody
    have hsecond : nestedRun^[1 + r.cost pa pb + 1]
        (some { l := some (.inr .gateDriver), var := v, stk := liftStacks S C }) =
          some { l := some (.inr .gateDriver), var := v1, stk := liftStacks T C' } := by
      exact iterTwo nestedRun (1 + r.cost pa pb) 1 _ _ _ hfirst hdone
    refine ⟨U, D, ?_, hD1, ?_, ?_, htail6, htail7, htail11,
      htail12, htail0, htail1, htail2, htail3, htail4, ?_, ?_, htail10⟩
    · exact iterTwo nestedRun (1 + r.cost pa pb + 1) (gateListCost pa pb rs)
        _ _ _ hsecond htail
    · rw [hD0]
      simp [C', Function.update_of_ne]
    · rw [htailAcc, hacc]
      simp [SourceRecord.targetList, List.reverse_append, List.append_assoc]
    · rw [htail8, h8]
    · rw [htail9, h9]

end ShiTMOuterLift
