import «AMPUNI-piece-entry-param-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceEntry

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

theorem copy_marks_run_at (source : Fin 4) (dest : Fin 14)
    (hdest : dest ≠ 3) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsrc : S (.inr source) = List.replicate n Cell.mark) :
    ∃ (U : ∀ k, List (TopGam k)),
      (runAt source dest)^[n + 1]
        (some { l := some (.inr .copy), var := v, stk := S }) =
          some { l := some (.inr .restore), var := none, stk := U }
      ∧ U (.inr source) = []
      ∧ U (.inl (.inl dest)) =
          List.replicate n Cell.mark ++ S (.inl (.inl dest))
      ∧ U (.inl (.inl (3 : Fin 14))) =
          List.replicate n Cell.mark ++ S (.inl (.inl 3))
      ∧ ∀ j, j ≠ .inr source → j ≠ .inl (.inl dest) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  induction n generalizing v S with
  | zero =>
      have he : S (.inr source) = [] := by simpa using hsrc
      refine ⟨S, ?_, he, ?_, ?_, ?_⟩
      · exact copy_empty_step_at source dest v S he
      · simp
      · simp
      · intro j _ _ _
        rfl
  | succ n ih =>
      have hm : S (.inr source) =
          Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hsrc
      let T := Function.update
        (Function.update
          (Function.update S (.inr source) (List.replicate n Cell.mark))
          (.inl (.inl dest)) (Cell.mark :: S (.inl (.inl dest))))
        (.inl (.inl (3 : Fin 14)))
        (Cell.mark :: S (.inl (.inl (3 : Fin 14))))
      have hfirst : (runAt source dest)^[1]
          (some { l := some (.inr .copy), var := v, stk := S }) =
            some { l := some (.inr .copy), var := some Cell.mark, stk := T } := by
        exact copy_mark_step_at source dest v S _ hdest hm
      have hTsrc : T (.inr source) = List.replicate n Cell.mark := by
        simp [T]
      obtain ⟨U, hrun, h0, h1, h3, hframe⟩ :=
        ih (some Cell.mark) T hTsrc
      refine ⟨U, ?_, h0, ?_, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (iterTwo (runAt source dest) 1 (n + 1) _ _ _ hfirst hrun)
      · have hTdest : T (.inl (.inl dest)) =
            Cell.mark :: S (.inl (.inl dest)) := by
          simp [T, hdest, Ne.symm hdest]
        rw [h1, hTdest]
        simpa only [List.replicate_succ, List.cons_append] using
          replicate_mark_snoc n (S (.inl (.inl dest)))
      · have hT3 : T (.inl (.inl (3 : Fin 14))) =
            Cell.mark :: S (.inl (.inl 3)) := by simp [T]
        rw [h3, hT3]
        simpa only [List.replicate_succ, List.cons_append] using
          replicate_mark_snoc n (S (.inl (.inl 3)))
      · intro j hj0 hjd hj3
        rw [hframe j hj0 hjd hj3]
        simp [T, Function.update_of_ne hj3, Function.update_of_ne hjd,
          Function.update_of_ne hj0]

end ShiTMPieceEntry
