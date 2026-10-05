import «AMPUNI-mirror-init-copy-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMMirrorInit

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

theorem restore_run (table : Table) (xs : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hscratch : S (.inl (.inl (10 : Fin 14))) = xs) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[xs.length + 1]
        (some { l := some (restorePhase table), var := v, stk := S }) =
          some { l := some (nextPhase table), var := none, stk := U }
      ∧ U (.inl (.inl (10 : Fin 14))) = []
      ∧ U (.inl (.inl (sourceIndex table))) =
          xs.reverse ++ S (.inl (.inl (sourceIndex table)))
      ∧ ∀ j, j ≠ .inl (.inl (sourceIndex table)) →
          j ≠ .inl (.inl (10 : Fin 14)) → U j = S j := by
  induction xs generalizing v S with
  | nil =>
      refine ⟨S, ?_, hscratch, ?_, ?_⟩
      · exact restore_empty_step table v S hscratch
      · simp
      · intro j _ _
        rfl
  | cons cell xs ih =>
      let T := Function.update
        (Function.update S (.inl (.inl (10 : Fin 14))) xs)
        (.inl (.inl (sourceIndex table)))
          (cell :: S (.inl (.inl (sourceIndex table))))
      have hfirst : run^[1]
          (some { l := some (restorePhase table), var := v, stk := S }) =
            some { l := some (restorePhase table), var := some cell, stk := T } := by
        exact restore_cell_step table v S cell xs hscratch
      have hTscratch : T (.inl (.inl (10 : Fin 14))) = xs := by
        cases table <;> simp [T, sourceIndex]
      obtain ⟨U, hrun, hU10, hUsrc, hframe⟩ :=
        ih (some cell) T hTscratch
      refine ⟨U, ?_, hU10, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (iterTwo run 1 (xs.length + 1) _ _ _ hfirst hrun)
      · have hTsrc : T (.inl (.inl (sourceIndex table))) =
            cell :: S (.inl (.inl (sourceIndex table))) := by
          cases table <;> simp [T, sourceIndex]
        rw [hUsrc, hTsrc]
        simp [List.reverse_cons, List.append_assoc]
      · intro j hj0 hj10
        rw [hframe j hj0 hj10]
        simp [T, Function.update_of_ne hj0,
          Function.update_of_ne hj10]

end ShiTMMirrorInit
