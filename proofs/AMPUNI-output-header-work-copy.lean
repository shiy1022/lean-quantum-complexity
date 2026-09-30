import «AMPUNI-output-header-work-step»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputHeader

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

theorem work_copy_marks_run (pc : PC) (atom : Atom) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsrc : S (.inr (source atom)) = List.replicate n Cell.mark) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[n + 1]
        (some { l := some (.work pc atom .copy), var := v, stk := S }) =
          some { l := some (.work pc atom .restore), var := none, stk := U }
      ∧ U (.inr (source atom)) = []
      ∧ U (.inl (.inl (13 : Fin 14))) =
          List.replicate n Cell.mark ++ S (.inl (.inl (13 : Fin 14)))
      ∧ U (.inl (.inl (3 : Fin 14))) =
          List.replicate n Cell.mark ++ S (.inl (.inl (3 : Fin 14)))
      ∧ ∀ j, j ≠ .inr (source atom) →
          j ≠ .inl (.inl (13 : Fin 14)) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  induction n generalizing v S with
  | zero =>
      have he : S (.inr (source atom)) = [] := by simpa using hsrc
      refine ⟨S, ?_, he, ?_, ?_, ?_⟩
      · exact work_copy_empty_step pc atom v S he
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
          (.inl (.inl (13 : Fin 14)))
            (Cell.mark :: S (.inl (.inl (13 : Fin 14)))))
        (.inl (.inl (3 : Fin 14)))
          (Cell.mark :: S (.inl (.inl (3 : Fin 14))))
      have hfirst : run^[1]
          (some { l := some (.work pc atom .copy), var := v, stk := S }) =
            some { l := some (.work pc atom .copy), var := some Cell.mark, stk := T } := by
        exact work_copy_mark_step pc atom v S _ hm
      have hTsrc : T (.inr (source atom)) = List.replicate n Cell.mark := by
        simp [T]
      obtain ⟨U, hrun, h0, h13, h3, hframe⟩ :=
        ih (some Cell.mark) T hTsrc
      refine ⟨U, ?_, h0, ?_, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (iterTwo run 1 (n + 1) _ _ _ hfirst hrun)
      · have hT13 : T (.inl (.inl (13 : Fin 14))) =
            Cell.mark :: S (.inl (.inl (13 : Fin 14))) := by simp [T]
        rw [h13, hT13]
        simpa only [List.replicate_succ, List.cons_append] using
          replicate_mark_snoc n (S (.inl (.inl (13 : Fin 14))))
      · have hT3 : T (.inl (.inl (3 : Fin 14))) =
            Cell.mark :: S (.inl (.inl (3 : Fin 14))) := by simp [T]
        rw [h3, hT3]
        simpa only [List.replicate_succ, List.cons_append] using
          replicate_mark_snoc n (S (.inl (.inl (3 : Fin 14))))
      · intro j hj0 hj13 hj3
        rw [hframe j hj0 hj13 hj3]
        simp [T, Function.update_of_ne hj3, Function.update_of_ne hj13,
          Function.update_of_ne hj0]

end ShiTMOutputHeader
