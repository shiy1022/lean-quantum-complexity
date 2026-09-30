import «AMPUNI-nested-machine»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOuterLift

open ShiTMLayoutMachine

private theorem localRun_none_iter (n : Nat) : localRun^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simpa [localRun] using ih

private theorem nested_step_agrees_before_done
    (C : Fin 2 → List Cell) (c : Cfg Gam Label Sig)
    (hc : c.l ≠ some (b .instructionDone)) :
    nestedRun (some (liftCfg C c)) =
      (localRun (some c)).map (liftCfg C) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      have hl : l ≠ b .instructionDone := by
        intro h
        exact hc (by simpa [h])
      simpa [nestedRun, localRun, liftCfg, step, nestedMachine,
        loopMachine, hl] using (stepAux_liftStmt (machine l) v S C)

/-- Any exact instruction-body run of the original machine is replayed on the nested
machine with both counter stacks untouched. The only changed body label is the endpoint. -/
theorem nested_transport_to_instructionDone (C : Fin 2 → List Cell) (n : Nat)
    (start finish : Cfg Gam Label Sig)
    (hfinish : finish.l = some (b .instructionDone))
    (hrun : localRun^[n] (some start) = some finish) :
    nestedRun^[n] (some (liftCfg C start)) =
      some (liftCfg C finish) := by
  induction n generalizing start with
  | zero =>
    have h : start = finish := by simpa using hrun
    subst finish
    rfl
  | succ n ih =>
    have hnot : start.l ≠ some (b .instructionDone) := by
      intro hdone
      cases start with
      | mk l v S =>
        have hl : l = some (b .instructionDone) := hdone
        subst l
        rw [Function.iterate_succ_apply] at hrun
        have hhalt : localRun (some { l := some (b .instructionDone), var := v, stk := S }) =
            some { l := none, var := v, stk := S } := by rfl
        rw [hhalt] at hrun
        cases n with
        | zero =>
          have heq : ({ l := none, var := v, stk := S } : Cfg Gam Label Sig) = finish := by
            simpa using hrun
          have hbad := congrArg Cfg.l heq
          rw [hfinish] at hbad
          cases hbad
        | succ m =>
          rw [Function.iterate_succ_apply] at hrun
          have hhalted : localRun (some { l := none, var := v, stk := S }) = none := by rfl
          rw [hhalted, localRun_none_iter] at hrun
          cases hrun
    rw [Function.iterate_succ_apply] at hrun ⊢
    rw [nested_step_agrees_before_done C start hnot]
    cases hstep : localRun (some start) with
    | none =>
      rw [hstep, localRun_none_iter] at hrun
      cases hrun
    | some middle =>
      exact ih middle (by simpa [hstep] using hrun)

end ShiTMOuterLift
