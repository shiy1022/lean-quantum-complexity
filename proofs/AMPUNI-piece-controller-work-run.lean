import «AMPUNI-piece-controller-work-restore»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry ShiTMPieceSchedule

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- A retained-field `add` command completes in `2*n+3` work steps. It
preserves its unary source, empties scratch, prepends exactly `n` marks to the
selected layout table, and returns to the next command dispatch slot. -/
theorem work_field_run (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsource : S (.inr (source atom)) = List.replicate n Cell.mark)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[2 * n + 3]
        (some { l := some (.work copy pc atom table .copy), var := v, stk := S }) =
          some { l := some (.dispatch copy (nextPC pc)), var := none, stk := U }
      ∧ U (.inr (source atom)) = List.replicate n Cell.mark
      ∧ U (.inl (.inl (destination table))) =
          List.replicate n Cell.mark ++ S (.inl (.inl (destination table)))
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, j ≠ .inr (source atom) →
          j ≠ .inl (.inl (destination table)) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  obtain ⟨C, hcopy, hCsource, hCdest, hCscratch, hCframe⟩ :=
    work_copy_marks_run copy pc atom table n v S hsource
  have hCscratch' : C (.inl (.inl (3 : Fin 14))) =
      List.replicate n Cell.mark := by
    simpa [hscratch] using hCscratch
  obtain ⟨U, hrestore, hUscratch, hUsource, hUframe⟩ :=
    work_restore_marks_run copy pc atom table n none C hCscratch'
  refine ⟨U, ?_, ?_, ?_, hUscratch, ?_⟩
  · have hfirst := iterTwo run (n + 1) (n + 1) _ _ _ hcopy hrestore
    have hlast := work_done_step copy pc atom table none U
    have hall := iterTwo run ((n + 1) + (n + 1)) 1 _ _ _ hfirst hlast
    have hcost : ((n + 1) + (n + 1)) + 1 = 2 * n + 3 := by omega
    simpa only [hcost] using hall
  · rw [hUsource, hCsource]
    simp
  · have hd : (.inl (.inl (destination table)) : TopK) ≠
        .inl (.inl (3 : Fin 14)) := by
      cases table <;> decide
    rw [hUframe (.inl (.inl (destination table))) (by simp) hd, hCdest]
  · intro j hj0 hjd hj3
    rw [hUframe j hj0 hj3, hCframe j hj0 hjd hj3]

/-- Including the dispatch jump, an active retained-field command takes
`2*n+4` controller steps. -/
theorem dispatch_field_run (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hcommand : commandAt (program copy) pc.val = some (.add table atom))
    (hone : atom ≠ .one)
    (hsource : S (.inr (source atom)) = List.replicate n Cell.mark)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      run^[2 * n + 4]
        (some { l := some (.dispatch copy pc), var := v, stk := S }) =
          some { l := some (.dispatch copy (nextPC pc)), var := none, stk := U }
      ∧ U (.inr (source atom)) = List.replicate n Cell.mark
      ∧ U (.inl (.inl (destination table))) =
          List.replicate n Cell.mark ++ S (.inl (.inl (destination table)))
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, j ≠ .inr (source atom) →
          j ≠ .inl (.inl (destination table)) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  obtain ⟨U, hrun, hsrc, hdest, hscratch', hframe⟩ :=
    work_field_run copy pc atom table n v S hsource hscratch
  refine ⟨U, ?_, hsrc, hdest, hscratch', hframe⟩
  have hfirst := dispatch_field_step copy pc atom table v S hcommand hone
  have hall := iterTwo run 1 (2 * n + 3) _ _ _ hfirst hrun
  have hcost : 1 + (2 * n + 3) = 2 * n + 4 := by omega
  simpa only [hcost] using hall

end ShiTMPieceController
