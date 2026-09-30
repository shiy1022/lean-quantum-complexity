import «AMPUNI-piece-entry-param-restore»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceEntry

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- A selectable retained unary field supplies one `marks ++ delimiter` table entry.
The source field and all non-participating stacks are preserved, scratch is emptied, and
the exact runtime is linear in the field value. -/
theorem piece_entry_run_at (source : Fin 4) (dest : Fin 14)
    (hdest : dest ≠ 3) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsource : S (.inr source) = List.replicate n Cell.mark)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      (runAt source dest)^[2 * n + 3]
        (some { l := some (.inr .start), var := v, stk := S }) =
          some { l := some (.inr .done), var := none, stk := U }
      ∧ U (.inr source) = List.replicate n Cell.mark
      ∧ U (.inl (.inl dest)) =
          List.replicate n Cell.mark ++ .delim :: S (.inl (.inl dest))
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, j ≠ .inr source → j ≠ .inl (.inl dest) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  let T := Function.update S (.inl (.inl dest))
    (Cell.delim :: S (.inl (.inl dest)))
  have hstart : (runAt source dest)^[1]
      (some { l := some (.inr .start), var := v, stk := S }) =
        some { l := some (.inr .copy), var := v, stk := T } :=
    start_step_at source dest v S
  have hTsource : T (.inr source) = List.replicate n Cell.mark := by
    simpa [T] using hsource
  obtain ⟨C, hcopy, hCsource, hCdest, hCscratch, hCframe⟩ :=
    copy_marks_run_at source dest hdest n v T hTsource
  have hCscratch' : C (.inl (.inl (3 : Fin 14))) =
      List.replicate n Cell.mark := by
    have hkey : (.inl (.inl (3 : Fin 14)) : TopK) ≠
        .inl (.inl dest) := by simpa using Ne.symm hdest
    have hT : T (.inl (.inl (3 : Fin 14))) =
        S (.inl (.inl (3 : Fin 14))) := by
      simp [T, Function.update_of_ne hkey]
    rw [hCscratch, hT, hscratch]
    simp
  obtain ⟨U, hrestore, hUscratch, hUsource, hUframe⟩ :=
    restore_marks_run_at source dest n none C hCscratch'
  refine ⟨U, ?_, ?_, ?_, hUscratch, ?_⟩
  · have hfirst := iterTwo (runAt source dest) 1 (n + 1)
      _ _ _ hstart hcopy
    have hall := iterTwo (runAt source dest) (1 + (n + 1)) (n + 1)
      _ _ _ hfirst hrestore
    have hcost : (1 + (n + 1)) + (n + 1) = 2 * n + 3 := by omega
    simpa only [hcost] using hall
  · rw [hUsource, hCsource]
    simp
  · have hd : (.inl (.inl dest) : TopK) ≠ .inl (.inl (3 : Fin 14)) := by
      simp [hdest]
    rw [hUframe (.inl (.inl dest)) (by simp) hd, hCdest]
    simp [T]
  · intro j hj0 hjd hj3
    rw [hUframe j hj0 hj3, hCframe j hj0 hjd hj3]
    simp [T, Function.update_of_ne hjd]

end ShiTMPieceEntry
