import «AMPUNI-piece-param-work-step»
import «AMPUNI-piece-tail-program»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceParam

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceEntry ShiTMPieceSchedule
open ShiTMPieceController

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The parameterized controller reuses the checked unary-copy steps for any
fixed command list, including the final one-wire tail program. -/
theorem work_copy_run (commands : List Command) (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsrc : S (.inr (source atom)) = List.replicate n Cell.mark) :
    ∃ (U : ∀ k, List (TopGam k)),
      (runFor commands)^[n + 1]
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
      · exact work_step_transfer commands copy pc atom table .copy v S _
          (ShiTMPieceController.work_copy_empty_step copy pc atom table v S he)
      · simp
      · simp
      · intro j _ _ _; rfl
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
      have hfirst : (runFor commands)^[1]
          (some { l := some (.work copy pc atom table .copy), var := v, stk := S }) =
            some { l := some (.work copy pc atom table .copy), var := some Cell.mark, stk := T } := by
        exact work_step_transfer commands copy pc atom table .copy v S _
          (ShiTMPieceController.work_copy_mark_step copy pc atom table v S _ hm)
      have hTsrc : T (.inr (source atom)) = List.replicate n Cell.mark := by
        simp [T]
      obtain ⟨U, hrun, h0, h1, h3, hframe⟩ :=
        ih (some Cell.mark) T hTsrc
      refine ⟨U, ?_, h0, ?_, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (iterTwo (runFor commands) 1 (n + 1) _ _ _ hfirst hrun)
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

theorem work_restore_run (commands : List Command) (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hscratch : S (.inl (.inl (3 : Fin 14))) = List.replicate n Cell.mark) :
    ∃ (U : ∀ k, List (TopGam k)),
      (runFor commands)^[n + 1]
        (some { l := some (.work copy pc atom table .restore), var := v, stk := S }) =
          some { l := some (.work copy pc atom table .done), var := none, stk := U }
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ U (.inr (source atom)) =
          List.replicate n Cell.mark ++ S (.inr (source atom))
      ∧ ∀ j, j ≠ .inr (source atom) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  induction n generalizing v S with
  | zero =>
      have he : S (.inl (.inl (3 : Fin 14))) = [] := by simpa using hscratch
      refine ⟨S, ?_, he, ?_, ?_⟩
      · exact work_step_transfer commands copy pc atom table .restore v S _
          (ShiTMPieceController.work_restore_empty_step copy pc atom table v S he)
      · simp
      · intro j _ _; rfl
  | succ n ih =>
      have hm : S (.inl (.inl (3 : Fin 14))) =
          Cell.mark :: List.replicate n Cell.mark := by
        simpa [List.replicate_succ] using hscratch
      let T := Function.update
        (Function.update S (.inl (.inl (3 : Fin 14)))
          (List.replicate n Cell.mark))
        (.inr (source atom)) (Cell.mark :: S (.inr (source atom)))
      have hfirst : (runFor commands)^[1]
          (some { l := some (.work copy pc atom table .restore), var := v, stk := S }) =
            some { l := some (.work copy pc atom table .restore), var := some Cell.mark, stk := T } := by
        exact work_step_transfer commands copy pc atom table .restore v S _
          (ShiTMPieceController.work_restore_mark_step copy pc atom table v S _ hm)
      have hTscratch : T (.inl (.inl (3 : Fin 14))) =
          List.replicate n Cell.mark := by simp [T]
      obtain ⟨U, hrun, h3, h0, hframe⟩ :=
        ih (some Cell.mark) T hTscratch
      refine ⟨U, ?_, h3, ?_, ?_⟩
      · simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (iterTwo (runFor commands) 1 (n + 1) _ _ _ hfirst hrun)
      · have hT0 : T (.inr (source atom)) =
            Cell.mark :: S (.inr (source atom)) := by simp [T]
        rw [h0, hT0]
        simpa only [List.replicate_succ, List.cons_append] using
          replicate_mark_snoc n (S (.inr (source atom)))
      · intro j hj0 hj3
        rw [hframe j hj0 hj3]
        simp [T, Function.update_of_ne hj0, Function.update_of_ne hj3]

/-- An entire retained-field work phase, independent of the selected program. -/
theorem work_field_run (commands : List Command) (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsource : S (.inr (source atom)) = List.replicate n Cell.mark)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      (runFor commands)^[2 * n + 3]
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
    work_copy_run commands copy pc atom table n v S hsource
  have hCscratch' : C (.inl (.inl (3 : Fin 14))) =
      List.replicate n Cell.mark := by
    simpa [hscratch] using hCscratch
  obtain ⟨U, hrestore, hUscratch, hUsource, hUframe⟩ :=
    work_restore_run commands copy pc atom table n none C hCscratch'
  refine ⟨U, ?_, ?_, ?_, hUscratch, ?_⟩
  · have hfirst := iterTwo (runFor commands) (n + 1) (n + 1)
      _ _ _ hcopy hrestore
    have hlast := ShiTMPieceParam.work_done_step commands copy pc atom table none U
    have hall := iterTwo (runFor commands) ((n + 1) + (n + 1)) 1
      _ _ _ hfirst hlast
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

/-- Including its dispatch jump, a retained-field command takes `2*n+4`
steps in the parameterized finite controller. -/
theorem dispatch_field_run (commands : List Command) (copy : Fin 3) (pc : PC)
    (atom : Atom) (table : Table) (n : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hcommand : commandAt commands pc.val = some (.add table atom))
    (hone : atom ≠ .one)
    (hsource : S (.inr (source atom)) = List.replicate n Cell.mark)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      (runFor commands)^[2 * n + 4]
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
    work_field_run commands copy pc atom table n v S hsource hscratch
  refine ⟨U, ?_, hsrc, hdest, hscratch', hframe⟩
  have hfirst := ShiTMPieceParam.dispatch_field_step
    commands copy pc atom table v S hcommand hone
  have hall := iterTwo (runFor commands) 1 (2 * n + 3)
    _ _ _ hfirst hrun
  have hcost : 1 + (2 * n + 3) = 2 * n + 4 := by omega
  simpa only [hcost] using hall

end ShiTMPieceParam
