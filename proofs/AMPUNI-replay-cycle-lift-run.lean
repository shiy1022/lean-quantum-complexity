import «AMPUNI-replay-cycle-lift-step»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayCycle

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

/-- A lifted subroutine run is unchanged up to, and including, its terminal
label. The combined machine is allowed to give that terminal label a new
outgoing transition because the subroutine run has not taken it yet. -/
private theorem lift_to_terminal {A : Type}
    (smallRun : Option (Cfg TopGam A Sig) → Option (Cfg TopGam A Sig))
    (f : A → CycleLabel) (terminal : A)
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

theorem split_run_lift (n : Nat)
    (c : Option (Cfg TopGam Bool Sig))
    (d : Cfg TopGam Bool Sig) (hd : d.l = some true)
    (hrun : ShiTMReplayMarkSplit.run^[n] c = some d) :
    run^[n] (c.map (liftCfg splitLabel)) =
      some (liftCfg splitLabel d) := by
  apply lift_to_terminal ShiTMReplayMarkSplit.run splitLabel true
    (by rfl) (by intros; rfl) (by intros; rfl) ?_ n c d hd hrun
  intro l v S hl
  cases l with
  | false => exact split_false_step v S
  | true => simp at hl

theorem reload_run_lift (n : Nat)
    (c : Option (Cfg TopGam ShiTMReplayReload.ReloadLabel Sig))
    (d : Cfg TopGam ShiTMReplayReload.ReloadLabel Sig)
    (hd : d.l = some 2)
    (hrun : ShiTMReplayReload.run^[n] c = some d) :
    run^[n] (c.map (liftCfg reloadLabel)) =
      some (liftCfg reloadLabel d) := by
  apply lift_to_terminal ShiTMReplayReload.run reloadLabel 2
    (by rfl) (by intros; rfl) (by intros; rfl) ?_ n c d hd hrun
  intro l v S hl
  fin_cases l
  · exact reload_zero_step v S
  · exact reload_one_step v S
  · simp at hl

theorem restore_run_lift (n : Nat)
    (c : Option (Cfg TopGam Bool Sig))
    (d : Cfg TopGam Bool Sig) (hd : d.l = some true)
    (hrun : ShiTMReplayMarkRestore.run^[n] c = some d) :
    run^[n] (c.map (liftCfg restoreLabel)) =
      some (liftCfg restoreLabel d) := by
  apply lift_to_terminal ShiTMReplayMarkRestore.run restoreLabel true
    (by rfl) (by intros; rfl) (by intros; rfl) ?_ n c d hd hrun
  intro l v S hl
  cases l with
  | false => exact restore_false_step v S
  | true => simp at hl

end ShiTMReplayCycle
