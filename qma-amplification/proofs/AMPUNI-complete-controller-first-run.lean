import «AMPUNI-complete-controller-lifts»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMCompleteController

open ShiTMLayoutMachine ShiTMRetainedTop

theorem preface_exit_halts (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    ShiTMReplayPreface.run
      (some ⟨some firstExit, v, S⟩) =
        some ⟨none, v, S⟩ := by
  rfl

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

/-- A preface run ending at the first parser exit lifts unchanged into the
combined controller. The next combined-machine step performs the handoff. -/
theorem first_run_lift (n : Nat)
    (c : Option (Cfg TopGam ShiTMReplayPreface.ReplayLabel Sig))
    (d : Cfg TopGam ShiTMReplayPreface.ReplayLabel Sig)
    (hd : d.l = some firstExit)
    (hrun : ShiTMReplayPreface.run^[n] c = some d) :
    run^[n] (c.map (liftCfg firstLabel)) =
      some (liftCfg firstLabel d) := by
  induction n generalizing c with
  | zero => simpa using congrArg (Option.map (liftCfg firstLabel)) hrun
  | succ n ih =>
      rw [Function.iterate_succ_apply] at hrun ⊢
      cases c with
      | none =>
          rw [show ShiTMReplayPreface.run none = none by rfl,
            iterate_none ShiTMReplayPreface.run rfl] at hrun
          cases hrun
      | some cfg =>
          cases cfg with
          | mk l v S =>
              cases l with
              | none =>
                  rw [show ShiTMReplayPreface.run
                      (some ⟨none, v, S⟩) = none by rfl,
                    iterate_none ShiTMReplayPreface.run rfl] at hrun
                  cases hrun
              | some l =>
                  by_cases hl : l = firstExit
                  · subst l
                    rw [preface_exit_halts] at hrun
                    cases n with
                    | zero =>
                        simp only [Function.iterate_zero, id_eq] at hrun
                        have heq := congrArg Cfg.l (Option.some.inj hrun)
                        simp [hd] at heq
                    | succ n =>
                        rw [iterate_halted ShiTMReplayPreface.run rfl
                          (by intros; rfl) n v S] at hrun
                        cases hrun
                  · simp only [Option.map_some]
                    change run^[n]
                      (run (some ⟨some (firstLabel l), v, S⟩)) =
                        some (liftCfg firstLabel d)
                    rw [first_nonterminal_step l hl v S]
                    exact ih (ShiTMReplayPreface.run
                      (some ⟨some l, v, S⟩)) hrun

end ShiTMCompleteController
