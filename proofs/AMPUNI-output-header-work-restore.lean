import «AMPUNI-output-header-work-copy»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputHeader

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

theorem work_restore_marks_run (pc : PC) (atom : Atom) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hscratch : S (.inl (.inl (3 : Fin 14))) =
      List.replicate n Cell.mark) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[n + 1]
        (some { l := some (.work pc atom .restore), var := v, stk := S }) =
          some { l := some (.work pc atom .done), var := none, stk := U }
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ U (.inr (source atom)) =
          List.replicate n Cell.mark ++ S (.inr (source atom))
      ∧ ∀ j, j ≠ .inr (source atom) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  induction n generalizing v S with
  | zero =>
      have he : S (.inl (.inl (3 : Fin 14))) = [] := by simpa using hscratch
      refine ⟨S, ?_, he, ?_, ?_⟩
      · exact work_restore_empty_step pc atom v S he
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
        (.inr (source atom)) (Cell.mark :: S (.inr (source atom)))
      have hfirst : run^[1]
          (some { l := some (.work pc atom .restore), var := v, stk := S }) =
            some { l := some (.work pc atom .restore), var := some Cell.mark, stk := T } := by
        exact work_restore_mark_step pc atom v S _ hm
      have hTscratch : T (.inl (.inl (3 : Fin 14))) =
          List.replicate n Cell.mark := by simp [T]
      obtain ⟨U, hrun, h3, h0, hframe⟩ :=
        ih (some Cell.mark) T hTscratch
      refine ⟨U, ?_, h3, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (iterTwo run 1 (n + 1) _ _ _ hfirst hrun)
      · have hT0 : T (.inr (source atom)) =
            Cell.mark :: S (.inr (source atom)) := by simp [T]
        rw [h0, hT0]
        simpa only [List.replicate_succ, List.cons_append] using
          replicate_mark_snoc n (S (.inr (source atom)))
      · intro j hj0 hj3
        rw [hframe j hj0 hj3]
        simp [T, Function.update_of_ne hj0, Function.update_of_ne hj3]

end ShiTMOutputHeader
