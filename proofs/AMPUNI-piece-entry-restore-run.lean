import «AMPUNI-piece-entry-copy-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceEntry

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The restore phase transfers all scratch marks back to the retained field stack,
leaving the newly constructed piece entry intact. -/
theorem restore_marks_run (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hscratch : S (.inl (.inl (3 : Fin 14))) = List.replicate n Cell.mark) :
    ∃ (U : ∀ k, List (TopGam k)),
      entryRun^[n + 1]
        (some { l := some (.inr .restore), var := v, stk := S }) =
          some { l := some (.inr .done), var := none, stk := U }
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ U (.inr (0 : Fin 4)) =
          List.replicate n Cell.mark ++ S (.inr 0)
      ∧ U (.inl (.inl (1 : Fin 14))) = S (.inl (.inl 1))
      ∧ ∀ j, j ≠ .inr (0 : Fin 4) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  induction n generalizing v S with
  | zero =>
      have he : S (.inl (.inl (3 : Fin 14))) = [] := by simpa using hscratch
      refine ⟨S, ?_, he, ?_, rfl, ?_⟩
      · exact entry_restore_empty_step v S he
      · simp
      · intro j _ _
        rfl
  | succ n ih =>
      have hm : S (.inl (.inl (3 : Fin 14))) =
          Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hscratch
      let T := Function.update
        (Function.update S (.inl (.inl (3 : Fin 14)))
          (List.replicate n Cell.mark))
        (.inr (0 : Fin 4)) (Cell.mark :: S (.inr (0 : Fin 4)))
      have hfirst : entryRun^[1]
          (some { l := some (.inr .restore), var := v, stk := S }) =
            some { l := some (.inr .restore), var := some Cell.mark, stk := T } := by
        exact entry_restore_mark_step v S _ hm
      have hTscratch : T (.inl (.inl (3 : Fin 14))) =
          List.replicate n Cell.mark := by simp [T]
      obtain ⟨U, hrun, h3, h0, h1, hframe⟩ :=
        ih (some Cell.mark) T hTscratch
      refine ⟨U, ?_, h3, ?_, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (iterTwo entryRun 1 (n + 1) _ _ _ hfirst hrun)
      · have hT0 : T (.inr (0 : Fin 4)) =
            Cell.mark :: S (.inr 0) := by simp [T]
        rw [h0, hT0]
        simpa only [List.replicate_succ, List.cons_append] using
          replicate_mark_snoc n (S (.inr 0))
      · rw [h1]
        simp [T]
      · intro j hj0 hj3
        rw [hframe j hj0 hj3]
        simp [T, Function.update_of_ne hj0, Function.update_of_ne hj3]

end ShiTMPieceEntry
