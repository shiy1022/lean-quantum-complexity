import «AMPUNI-mirror-init-step»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMMirrorInit

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

theorem copy_run (table : Table) (xs : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsrc : S (.inl (.inl (sourceIndex table))) = xs) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[xs.length + 1]
        (some { l := some (copyPhase table), var := v, stk := S }) =
          some { l := some (restorePhase table), var := none, stk := U }
      ∧ U (.inl (.inl (sourceIndex table))) = []
      ∧ U (.inl (.inl (mirrorIndex table))) =
          xs.reverse ++ S (.inl (.inl (mirrorIndex table)))
      ∧ U (.inl (.inl (10 : Fin 14))) =
          xs.reverse ++ S (.inl (.inl (10 : Fin 14)))
      ∧ ∀ j, j ≠ .inl (.inl (sourceIndex table)) →
          j ≠ .inl (.inl (mirrorIndex table)) →
          j ≠ .inl (.inl (10 : Fin 14)) → U j = S j := by
  induction xs generalizing v S with
  | nil =>
      refine ⟨S, ?_, hsrc, ?_, ?_, ?_⟩
      · exact copy_empty_step table v S hsrc
      · simp
      · simp
      · intro j _ _ _
        rfl
  | cons cell xs ih =>
      let T := Function.update
        (Function.update
          (Function.update S (.inl (.inl (sourceIndex table))) xs)
          (.inl (.inl (mirrorIndex table)))
            (cell :: S (.inl (.inl (mirrorIndex table)))))
        (.inl (.inl (10 : Fin 14)))
          (cell :: S (.inl (.inl (10 : Fin 14))))
      have hfirst : run^[1]
          (some { l := some (copyPhase table), var := v, stk := S }) =
            some { l := some (copyPhase table), var := some cell, stk := T } := by
        exact copy_cell_step table v S cell xs hsrc
      have hTsrc : T (.inl (.inl (sourceIndex table))) = xs := by
        cases table <;> simp [T, sourceIndex, mirrorIndex]
      obtain ⟨U, hrun, hUsrc, hUmirror, hUscratch, hframe⟩ :=
        ih (some cell) T hTsrc
      refine ⟨U, ?_, hUsrc, ?_, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (iterTwo run 1 (xs.length + 1) _ _ _ hfirst hrun)
      · have hTm : T (.inl (.inl (mirrorIndex table))) =
            cell :: S (.inl (.inl (mirrorIndex table))) := by
          cases table <;> simp [T, sourceIndex, mirrorIndex]
        rw [hUmirror, hTm]
        simp [List.reverse_cons, List.append_assoc]
      · have hT10 : T (.inl (.inl (10 : Fin 14))) =
            cell :: S (.inl (.inl (10 : Fin 14))) := by
          cases table <;> simp [T, sourceIndex, mirrorIndex]
        rw [hUscratch, hT10]
        simp [List.reverse_cons, List.append_assoc]
      · intro j hj0 hjm hj10
        rw [hframe j hj0 hjm hj10]
        simp [T, Function.update_of_ne hj10,
          Function.update_of_ne hjm, Function.update_of_ne hj0]

end ShiTMMirrorInit
