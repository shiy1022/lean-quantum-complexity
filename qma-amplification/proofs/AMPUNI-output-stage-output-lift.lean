import «AMPUNI-output-stage-lift»
import «AMPUNI-output-header-program-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputStage

open ShiTMLayoutMachine ShiTMRetainedTop

theorem output_step (l : ShiTMOutputHeader.Label) (v : Sig)
    (S : ∀ k, List (TopGam k)) (h : l ≠ .finished) :
    run (some { l := some (outputLabel l), var := v, stk := S }) =
      (ShiTMOutputHeader.run
        (some { l := some l, var := v, stk := S })).map
          (liftCfg outputLabel) := by
  cases l with
  | finished => exact (h rfl).elim
  | dispatch pc =>
      simp [run, machine, outputLabel, ShiTMOutputHeader.run, step,
        stepAux_liftStmt]
  | work pc atom phase =>
      simp [run, machine, outputLabel, ShiTMOutputHeader.run, step,
        stepAux_liftStmt]

private theorem iterate_none {A : Type} (f : Option A → Option A)
    (hf : f none = none) : ∀ n : Nat, f^[n] none = none
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply, hf]
      exact iterate_none f hf n

private theorem inactive_no_active (n : Nat)
    (c d : Cfg TopGam ShiTMOutputHeader.Label Sig)
    (hc : c.l = none) (hd : d.l ≠ none) :
    ShiTMOutputHeader.run^[n] (some c) ≠ some d := by
  cases c with
  | mk l v S =>
      cases l with
      | some l => cases hc
      | none =>
          cases n with
          | zero =>
              intro h
              have heq := Option.some.inj h
              subst d
              exact hd rfl
          | succ n =>
              intro h
              rw [Function.iterate_succ_apply] at h
              have hfirst : ShiTMOutputHeader.run
                  (some { l := none, var := v, stk := S }) = none := rfl
              rw [hfirst, iterate_none ShiTMOutputHeader.run (by rfl) n] at h
              cases h

/-- A run ending in an active output-controller label cannot previously
have visited `.finished`, because that label halts in the source machine. -/
theorem output_run_lift (n : Nat)
    (c d : Cfg TopGam ShiTMOutputHeader.Label Sig)
    (hd : d.l ≠ none)
    (hrun : ShiTMOutputHeader.run^[n] (some c) = some d) :
    run^[n] (some (liftCfg outputLabel c)) =
      some (liftCfg outputLabel d) := by
  induction n generalizing c with
  | zero =>
      have hcd : c = d := Option.some.inj hrun
      subst d
      rfl
  | succ n ih =>
      cases c with
      | mk cl v S =>
          cases cl with
          | none =>
              exact (inactive_no_active (n + 1)
                { l := none, var := v, stk := S } d rfl hd hrun).elim
          | some l =>
              rw [Function.iterate_succ_apply] at hrun
              change ShiTMOutputHeader.run^[n]
                (some (stepAux (ShiTMOutputHeader.machine l) v S)) =
                  some d at hrun
              by_cases hbad : l = .finished
              · subst l
                have hnone : (stepAux
                    (ShiTMOutputHeader.machine ShiTMOutputHeader.Label.finished)
                    v S).l = none := by rfl
                exact (inactive_no_active n
                  (stepAux (ShiTMOutputHeader.machine
                    ShiTMOutputHeader.Label.finished) v S)
                  d hnone hd hrun).elim
              · have hfirst := output_step l v S hbad
                have hrest := ih (stepAux (ShiTMOutputHeader.machine l) v S) hrun
                rw [Function.iterate_succ_apply]
                change run^[n]
                  (run (some { l := some (outputLabel l), var := v, stk := S })) =
                    some (liftCfg outputLabel d)
                rw [hfirst]
                simpa [ShiTMOutputHeader.run, step] using hrest

end ShiTMOutputStage
