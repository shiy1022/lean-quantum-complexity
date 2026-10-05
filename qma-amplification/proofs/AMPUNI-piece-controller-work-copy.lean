import «AMPUNI-piece-controller-work-local»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry ShiTMPieceSchedule

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The controller's copy phase consumes a retained unary field, adds its marks
to both the chosen layout stack and scratch, then enters restore. -/
theorem work_copy_marks_run (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsrc : S (.inr (source atom)) = List.replicate n Cell.mark) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[n + 1]
        (some { l := some (.work copy pc atom table .copy), var := v, stk := S }) =
          some { l := some (.work copy pc atom table .restore), var := none, stk := U }
      ∧ U (.inr (source atom)) = []
      ∧ U (.inl (.inl (destination table))) =
          List.replicate n Cell.mark ++ S (.inl (.inl (destination table)))
      ∧ U (.inl (.inl (3 : Fin 14))) =
          List.replicate n Cell.mark ++ S (.inl (.inl (3 : Fin 14)))
      ∧ ∀ j, j ≠ .inr (source atom) →
          j ≠ .inl (.inl (destination table)) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  induction n generalizing v S with
  | zero =>
      have he : S (.inr (source atom)) = [] := by simpa using hsrc
      refine ⟨S, ?_, he, ?_, ?_, ?_⟩
      · exact work_copy_empty_step copy pc atom table v S he
      · simp
      · simp
      · intro j _ _ _
        rfl
  | succ n ih =>
      have hm : S (.inr (source atom)) =
          Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hsrc
      let T := Function.update
        (Function.update
          (Function.update S (.inr (source atom)) (List.replicate n Cell.mark))
          (.inl (.inl (destination table)))
            (Cell.mark :: S (.inl (.inl (destination table)))))
        (.inl (.inl (3 : Fin 14)))
          (Cell.mark :: S (.inl (.inl (3 : Fin 14))))
      have hfirst : run^[1]
          (some { l := some (.work copy pc atom table .copy), var := v, stk := S }) =
            some { l := some (.work copy pc atom table .copy), var := some Cell.mark, stk := T } := by
        exact work_copy_mark_step copy pc atom table v S _ hm
      have hTsrc : T (.inr (source atom)) = List.replicate n Cell.mark := by
        simp [T]
      obtain ⟨U, hrun, h0, h1, h3, hframe⟩ :=
        ih (some Cell.mark) T hTsrc
      refine ⟨U, ?_, h0, ?_, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (iterTwo run 1 (n + 1) _ _ _ hfirst hrun)
      · have hTdest : T (.inl (.inl (destination table))) =
            Cell.mark :: S (.inl (.inl (destination table))) := by
          cases table <;> simp [T, destination]
        rw [h1, hTdest]
        simpa only [List.replicate_succ, List.cons_append] using
          replicate_mark_snoc n (S (.inl (.inl (destination table))))
      · have hT3 : T (.inl (.inl (3 : Fin 14))) =
            Cell.mark :: S (.inl (.inl 3)) := by
          cases table <;> simp [T, destination]
        rw [h3, hT3]
        simpa only [List.replicate_succ, List.cons_append] using
          replicate_mark_snoc n (S (.inl (.inl 3)))
      · intro j hj0 hjd hj3
        rw [hframe j hj0 hjd hj3]
        simp [T, Function.update_of_ne hj3, Function.update_of_ne hjd,
          Function.update_of_ne hj0]

end ShiTMPieceController
