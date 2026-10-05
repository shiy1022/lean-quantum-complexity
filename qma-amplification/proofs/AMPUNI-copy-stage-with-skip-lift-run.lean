import «AMPUNI-copy-stage-with-skip-step»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCopyStageWithSkip

open ShiTMLayoutMachine ShiTMRetainedTop

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

/-- A run ending at a subroutine's halt label is reproduced by the enclosing
machine. The enclosing machine may redirect that label on its next step. -/
private theorem lift_to_terminal {A : Type}
    (smallRun : Option (Cfg TopGam A Sig) → Option (Cfg TopGam A Sig))
    (f : A → Label) (terminal : A)
    (hNone : smallRun none = none)
    (hHalt : ∀ (v : Sig) (S : ∀ k, List (TopGam k)),
      smallRun (some ⟨none, v, S⟩) = none)
    (hTerminal : ∀ (v : Sig) (S : ∀ k, List (TopGam k)),
      smallRun (some ⟨some terminal, v, S⟩) =
        some ⟨none, v, S⟩)
    (hStep : ∀ (l : A) (v : Sig) (S : ∀ k, List (TopGam k)),
      l ≠ terminal →
      run (some (liftCfg f ⟨some l, v, S⟩)) =
        (smallRun (some ⟨some l, v, S⟩)).map (liftCfg f))
    (n : Nat) (c : Option (Cfg TopGam A Sig))
    (d : Cfg TopGam A Sig) (hd : d.l = some terminal)
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
                  by_cases hl : l = terminal
                  · subst l
                    rw [hTerminal] at hrun
                    cases n with
                    | zero =>
                        simp only [Function.iterate_zero, id_eq] at hrun
                        have heq := congrArg Cfg.l (Option.some.inj hrun)
                        simp [hd] at heq
                    | succ n =>
                        rw [iterate_halted smallRun hNone hHalt n v S] at hrun
                        cases hrun
                  · simp only [Option.map_some]
                    rw [hStep l v S hl]
                    exact ih (smallRun (some ⟨some l, v, S⟩)) hrun

theorem cycle_run_lift (copy : Fin 3) (n : Nat)
    (c : Option (Cfg TopGam ShiTMReplayCycle.CycleLabel Sig))
    (d : Cfg TopGam ShiTMReplayCycle.CycleLabel Sig)
    (hd : d.l = some (ShiTMReplayCycle.restoreLabel true))
    (hrun : ShiTMReplayCycle.run^[n] c = some d) :
    run^[n] (c.map (liftCfg
      (fun q => oldLabel (ShiTMCopyStage.cycleLabel copy q)))) =
      some (liftCfg
        (fun q => oldLabel (ShiTMCopyStage.cycleLabel copy q)) d) := by
  apply lift_to_terminal ShiTMReplayCycle.run
    (fun q => oldLabel (ShiTMCopyStage.cycleLabel copy q))
    (ShiTMReplayCycle.restoreLabel true)
    (by rfl) (by intros; rfl) (by intros; rfl) ?_ n c d hd hrun
  intro l v S hl
  exact cycle_nonterminal_step copy l hl v S

theorem skip_run_lift (copy : Fin 3) (n : Nat)
    (c : Option (Cfg TopGam ShiTMReplayHeaderSkip.Phase Sig))
    (d : Cfg TopGam ShiTMReplayHeaderSkip.Phase Sig)
    (hd : d.l = some 4)
    (hrun : ShiTMReplayHeaderSkip.run^[n] c = some d) :
    run^[n] (c.map (liftCfg (skipLabel copy))) =
      some (liftCfg (skipLabel copy) d) := by
  apply lift_to_terminal ShiTMReplayHeaderSkip.run
    (skipLabel copy) 4
    (by rfl) (by intros; rfl) (by intros; rfl) ?_ n c d hd hrun
  intro l v S hl
  exact skip_nonterminal_step copy l hl v S

theorem clear_run_lift (copy : Fin 3) (n : Nat)
    (c : Option (Cfg TopGam ShiTMReplayTableClear.Phase Sig))
    (d : Cfg TopGam ShiTMReplayTableClear.Phase Sig)
    (hd : d.l = some .done)
    (hrun : ShiTMReplayTableClear.run^[n] c = some d) :
    run^[n] (c.map (liftCfg
      (fun q => oldLabel (ShiTMCopyStage.clearLabel copy q)))) =
      some (liftCfg
        (fun q => oldLabel (ShiTMCopyStage.clearLabel copy q)) d) := by
  apply lift_to_terminal ShiTMReplayTableClear.run
    (fun q => oldLabel (ShiTMCopyStage.clearLabel copy q)) .done
    (by rfl) (by intros; rfl) (by intros; rfl) ?_ n c d hd hrun
  intro l v S hl
  exact clear_nonterminal_step copy l hl v S

end ShiTMCopyStageWithSkip
