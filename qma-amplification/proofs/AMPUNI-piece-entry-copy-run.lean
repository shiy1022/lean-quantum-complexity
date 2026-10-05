import «AMPUNI-piece-entry-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceEntry

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

theorem replicate_mark_snoc (n : Nat) (tail : List Cell) :
    List.replicate n Cell.mark ++ Cell.mark :: tail =
      Cell.mark :: (List.replicate n Cell.mark ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using congrArg (Cell.mark :: ·) ih

/-- The copy phase consumes a unary retained field, prepending its marks to both the
destination piece stack and the scratch stack. -/
theorem copy_marks_run (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsrc : S (.inr (0 : Fin 4)) = List.replicate n Cell.mark) :
    ∃ (U : ∀ k, List (TopGam k)),
      entryRun^[n + 1]
        (some { l := some (.inr .copy), var := v, stk := S }) =
          some { l := some (.inr .restore), var := none, stk := U }
      ∧ U (.inr (0 : Fin 4)) = []
      ∧ U (.inl (.inl (1 : Fin 14))) =
          List.replicate n Cell.mark ++ S (.inl (.inl 1))
      ∧ U (.inl (.inl (3 : Fin 14))) =
          List.replicate n Cell.mark ++ S (.inl (.inl 3))
      ∧ ∀ j, j ≠ .inr (0 : Fin 4) →
          j ≠ .inl (.inl (1 : Fin 14)) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  induction n generalizing v S with
  | zero =>
      have he : S (.inr (0 : Fin 4)) = [] := by simpa using hsrc
      refine ⟨S, ?_, he, ?_, ?_, ?_⟩
      · exact entry_copy_empty_step v S he
      · simp
      · simp
      · intro j _ _ _
        rfl
  | succ n ih =>
      have hm : S (.inr (0 : Fin 4)) =
          Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hsrc
      let T := Function.update
        (Function.update
          (Function.update S (.inr (0 : Fin 4)) (List.replicate n Cell.mark))
          (.inl (.inl (1 : Fin 14)))
          (Cell.mark :: S (.inl (.inl (1 : Fin 14)))))
        (.inl (.inl (3 : Fin 14)))
        (Cell.mark :: S (.inl (.inl (3 : Fin 14))))
      have hfirst : entryRun^[1]
          (some { l := some (.inr .copy), var := v, stk := S }) =
            some { l := some (.inr .copy), var := some Cell.mark, stk := T } := by
        exact entry_copy_mark_step v S _ hm
      have hTsrc : T (.inr (0 : Fin 4)) = List.replicate n Cell.mark := by
        simp [T]
      obtain ⟨U, hrun, h0, h1, h3, hframe⟩ := ih (some Cell.mark) T hTsrc
      refine ⟨U, ?_, h0, ?_, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (iterTwo entryRun 1 (n + 1) _ _ _ hfirst hrun)
      · have hT1 : T (.inl (.inl (1 : Fin 14))) =
            Cell.mark :: S (.inl (.inl 1)) := by simp [T]
        rw [h1, hT1]
        simpa only [List.replicate_succ, List.cons_append] using
          replicate_mark_snoc n (S (.inl (.inl 1)))
      · have hT3 : T (.inl (.inl (3 : Fin 14))) =
            Cell.mark :: S (.inl (.inl 3)) := by simp [T]
        rw [h3, hT3]
        simpa only [List.replicate_succ, List.cons_append] using
          replicate_mark_snoc n (S (.inl (.inl 3)))
      · intro j hj0 hj1 hj3
        rw [hframe j hj0 hj1 hj3]
        simp [T, Function.update_of_ne hj3, Function.update_of_ne hj1,
          Function.update_of_ne hj0]

end ShiTMPieceEntry
