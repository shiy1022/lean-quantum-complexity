import «AMPUNI-piece-entry-restore-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceEntry

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- One complete unary piece entry is built in `2n+3` steps. The retained source count
is restored, the scratch stack is empty, and the destination receives `n` marks and one
delimiter in front of its previous contents. -/
theorem piece_entry_run (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsource : S (.inr (0 : Fin 4)) = List.replicate n Cell.mark)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      entryRun^[2 * n + 3]
        (some { l := some (.inr .start), var := v, stk := S }) =
          some { l := some (.inr .done), var := none, stk := U }
      ∧ U (.inr (0 : Fin 4)) = List.replicate n Cell.mark
      ∧ U (.inl (.inl (1 : Fin 14))) =
          List.replicate n Cell.mark ++ .delim :: S (.inl (.inl 1))
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, j ≠ .inr (0 : Fin 4) →
          j ≠ .inl (.inl (1 : Fin 14)) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  let T := Function.update S (.inl (.inl (1 : Fin 14)))
    (Cell.delim :: S (.inl (.inl 1)))
  have hstart : entryRun^[1]
      (some { l := some (.inr .start), var := v, stk := S }) =
        some { l := some (.inr .copy), var := v, stk := T } :=
    entry_start_step v S
  have hTsource : T (.inr (0 : Fin 4)) = List.replicate n Cell.mark := by
    simpa [T] using hsource
  obtain ⟨C, hcopy, hCsource, hCdest, hCscratch, hCframe⟩ :=
    copy_marks_run n v T hTsource
  have hCscratch' : C (.inl (.inl (3 : Fin 14))) =
      List.replicate n Cell.mark := by
    rw [hCscratch]
    simp [T, hscratch]
  obtain ⟨U, hrestore, hUscratch, hUsource, hUdest, hUframe⟩ :=
    restore_marks_run n none C hCscratch'
  refine ⟨U, ?_, ?_, ?_, hUscratch, ?_⟩
  · have hfirst := iterTwo entryRun 1 (n + 1) _ _ _ hstart hcopy
    have hall := iterTwo entryRun (1 + (n + 1)) (n + 1)
      _ _ _ hfirst hrestore
    have hcost : (1 + (n + 1)) + (n + 1) = 2 * n + 3 := by omega
    simpa only [hcost] using hall
  · rw [hUsource, hCsource]
    simp
  · rw [hUdest, hCdest]
    simp [T]
  · intro j hj0 hj1 hj3
    rw [hUframe j hj0 hj3, hCframe j hj0 hj1 hj3]
    simp [T, Function.update_of_ne hj1]

end ShiTMPieceEntry
