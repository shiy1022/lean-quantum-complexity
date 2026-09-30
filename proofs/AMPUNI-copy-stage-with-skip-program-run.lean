import «AMPUNI-copy-stage-with-skip-program-step»
import «AMPUNI-piece-controller-frame-finish»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController ShiTMPieceSchedule

private theorem iterate_none {A : Type}
    (smallRun : Option (Cfg TopGam A Sig) → Option (Cfg TopGam A Sig))
    (hNone : smallRun none = none) (n : Nat) :
    smallRun^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, hNone]
      exact ih

private theorem iterate_halted {A : Type}
    (smallRun : Option (Cfg TopGam A Sig) → Option (Cfg TopGam A Sig))
    (hNone : smallRun none = none)
    (hHalt : ∀ (v : Sig) (S : ∀ k, List (TopGam k)),
      smallRun (some ⟨none, v, S⟩) = none)
    (n : Nat) (v : Sig) (S : ∀ k, List (TopGam k)) :
    smallRun^[n + 1] (some ⟨none, v, S⟩) = none := by
  rw [show n + 1 = Nat.succ n by omega,
    Function.iterate_succ_apply, hHalt]
  exact iterate_none smallRun hNone n

/-- A subroutine may have several terminal labels; none can be visited before
a successful run reaches its specified final label. -/
private theorem lift_to_terminal_pred {A : Type}
    (smallRun : Option (Cfg TopGam A Sig) → Option (Cfg TopGam A Sig))
    (f : A → Label) (terminal : A → Prop)
    (hNone : smallRun none = none)
    (hHalt : ∀ (v : Sig) (S : ∀ k, List (TopGam k)),
      smallRun (some ⟨none, v, S⟩) = none)
    (hTerminal : ∀ (l : A) (v : Sig) (S : ∀ k, List (TopGam k)),
      terminal l → smallRun (some ⟨some l, v, S⟩) =
        some ⟨none, v, S⟩)
    (hStep : ∀ (l : A) (v : Sig) (S : ∀ k, List (TopGam k)),
      ¬ terminal l →
      run (some (liftCfg f ⟨some l, v, S⟩)) =
        (smallRun (some ⟨some l, v, S⟩)).map (liftCfg f))
    (n : Nat) (c : Option (Cfg TopGam A Sig))
    (d : Cfg TopGam A Sig) (hd : d.l.isSome)
    (hrun : smallRun^[n] c = some d) :
    run^[n] (c.map (liftCfg f)) = some (liftCfg f d) := by
  induction n generalizing c with
  | zero =>
      simpa using congrArg (Option.map (liftCfg f)) hrun
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      cases c with
      | none =>
          rw [hNone, iterate_none smallRun hNone] at hrun
          cases hrun
      | some cfg =>
          cases cfg with
          | mk l v S =>
              cases l with
              | none =>
                  rw [hHalt, iterate_none smallRun hNone] at hrun
                  cases hrun
              | some l =>
                  by_cases hl : terminal l
                  · rw [hTerminal l v S hl] at hrun
                    cases n with
                    | zero =>
                        simp only [Function.iterate_zero, id_eq] at hrun
                        have heq := congrArg Cfg.l (Option.some.inj hrun)
                        have hnone : d.l = none := heq.symm
                        simp [hnone] at hd
                    | succ n =>
                        rw [iterate_halted smallRun hNone hHalt n v S] at hrun
                        cases hrun
                  · simp only [Option.map_some]
                    rw [hStep l v S hl]
                    exact ih (smallRun (some ⟨some l, v, S⟩)) hrun

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The already-proved finite piece program executes inside the corrected
copy-stage controller and hands off to mirror initialization. -/
theorem program_run_to_mirror (copy : Fin 3) (n wit anc : Nat)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig),
      run^[scheduleCost n wit anc (program copy) + 1 + 1]
        (some ⟨some (oldLabel (ShiTMCopyStage.programLabel copy
          (.dispatch copy 0))), v, S⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.mirrorLabel copy
          .startWidth)), v', U⟩
      ∧ tableState U = runCommands n wit anc (program copy) (tableState S)
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  obtain ⟨U, v', hprogram, htables, hretU, hscratchU, hframe⟩ :=
    run_program_finished_frame copy n wit anc v S hret hscratch
  have hprogram' : run^[scheduleCost n wit anc (program copy) + 1]
      (some ⟨some (oldLabel (ShiTMCopyStage.programLabel copy
        (.dispatch copy 0))), v, S⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.programLabel copy
          (.finished copy))), v', U⟩ := by
    have hLift := lift_to_terminal_pred ShiTMPieceController.run
      (fun q => oldLabel (ShiTMCopyStage.programLabel copy q))
      (fun q => ∃ actual : Fin 3, q = .finished actual)
      (by rfl) (by intros; rfl)
      (by intro l v S hl; rcases hl with ⟨actual, rfl⟩; rfl)
      (by
        intro l v S hl
        exact program_nonterminal_step copy l
          (fun actual h => hl ⟨actual, h⟩) v S)
      (scheduleCost n wit anc (program copy) + 1)
      (some ⟨some (ShiTMPieceController.Label.dispatch copy 0), v, S⟩)
      ⟨some (ShiTMPieceController.Label.finished copy), v', U⟩
      (show (some (ShiTMPieceController.Label.finished copy) :
        Option ShiTMPieceController.Label).isSome = true by rfl) hprogram
    simpa [liftCfg, oldLabel, ShiTMCopyStage.programLabel] using hLift
  have hmirror : run^[1]
      (some ⟨some (oldLabel (ShiTMCopyStage.programLabel copy
        (.finished copy))), v', U⟩) =
        some ⟨some (oldLabel (ShiTMCopyStage.mirrorLabel copy
          .startWidth)), v', U⟩ := by
    simpa using program_terminal_step copy copy v' U
  exact ⟨U, v', iterTwo run _ 1 _ _ _ hprogram' hmirror,
    htables, hretU, hscratchU, hframe⟩

end ShiTMCopyStageWithSkip
