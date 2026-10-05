import «AMPUNI-layout-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMLayoutMachine

/-- The instruction body is unchanged; only its terminal label rejoins the next parse. -/
def loopMachine (l : Label) : Stmt Gam Label Sig :=
  if l = b .instructionDone then Stmt.goto (fun _ => b .parseTag) else machine l

def localRun : Option (Cfg Gam Label Sig) → Option (Cfg Gam Label Sig) :=
  fun cf => cf.bind (step machine)

def loopRun : Option (Cfg Gam Label Sig) → Option (Cfg Gam Label Sig) :=
  fun cf => cf.bind (step loopMachine)

private theorem localRun_halted (v : Sig) (S : ∀ k, List (Gam k)) :
    localRun (some { l := none, var := v, stk := S }) = none := by
  rfl

private theorem localRun_none_iter (n : Nat) : localRun^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    simpa [localRun] using ih

private theorem localRun_done (v : Sig) (S : ∀ k, List (Gam k)) :
    localRun (some { l := some (b .instructionDone), var := v, stk := S }) =
      some { l := none, var := v, stk := S } := by
  rfl

private theorem loopRun_agrees (c : Cfg Gam Label Sig)
    (hc : c.l ≠ some (b .instructionDone)) :
    loopRun (some c) = localRun (some c) := by
  cases c with
  | mk l v S =>
    cases l with
    | none => rfl
    | some l =>
      have hl : l ≠ b .instructionDone := by
        intro h
        exact hc (by simpa [h])
      simp [loopRun, localRun, loopMachine, hl]

/-- A run that first reaches `instructionDone` at its stated endpoint can be replayed by
the looping machine: that endpoint is never stepped during the run. -/
theorem transport_run_to_instructionDone (n : Nat)
    (start finish : Cfg Gam Label Sig)
    (hfinish : finish.l = some (b .instructionDone))
    (hrun : localRun^[n] (some start) = some finish) :
    loopRun^[n] (some start) = some finish := by
  induction n generalizing start with
  | zero => exact hrun
  | succ n ih =>
    have hnot : start.l ≠ some (b .instructionDone) := by
      intro hdone
      cases start with
      | mk l v S =>
        have hl : l = some (b .instructionDone) := hdone
        subst l
        rw [Function.iterate_succ_apply, localRun_done] at hrun
        cases n with
        | zero =>
          have heq : ({ l := none, var := v, stk := S } : Cfg Gam Label Sig) = finish := by
            simpa using hrun
          have := congrArg Cfg.l heq
          rw [hfinish] at this
          cases this
        | succ m =>
          rw [Function.iterate_succ_apply, localRun_halted] at hrun
          rw [localRun_none_iter] at hrun
          cases hrun
    rw [Function.iterate_succ_apply] at hrun ⊢
    rw [loopRun_agrees start hnot]
    cases hstep : localRun (some start) with
    | none =>
      rw [hstep, localRun_none_iter] at hrun
      cases hrun
    | some middle =>
      exact ih middle (by simpa [hstep] using hrun)

theorem loopMachine_restart (v : Sig) (S : ∀ k, List (Gam k)) :
    loopRun^[1] (some { l := some (b .instructionDone), var := v, stk := S }) =
      some { l := some (b .parseTag), var := v, stk := S } := by
  rfl

end ShiTMLayoutMachine
