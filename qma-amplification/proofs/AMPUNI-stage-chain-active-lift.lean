import «AMPUNI-stage-chain-lift»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMStageChain

open ShiTMLayoutMachine ShiTMRetainedTop

def componentRun {A : Type} (M : A → Stmt TopGam A Sig) :
    Option (Cfg TopGam A Sig) → Option (Cfg TopGam A Sig) :=
  fun cf => cf.bind (step M)

private theorem iterate_none {A : Type} (f : Option A → Option A)
    (hf : f none = none) : ∀ n : Nat, f^[n] none = none
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply, hf]
      exact iterate_none f hf n

private theorem inactive_no_active {A : Type}
    (M : A → Stmt TopGam A Sig) (n : Nat)
    (c d : Cfg TopGam A Sig) (hc : c.l = none) (hd : d.l ≠ none) :
    (componentRun M)^[n] (some c) ≠ some d := by
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
              have hfirst : componentRun M
                  (some { l := none, var := v, stk := S }) = none := rfl
              rw [hfirst, iterate_none (componentRun M) (by rfl) n] at h
              cases h

/-- Generic exact-run lift through a machine that changes only what happens
*after* a terminal label. An active final source configuration cannot have
visited a terminal label earlier, since the source machine halts there. -/
theorem run_lift_active {A : Type} (M : A → Stmt TopGam A Sig)
    (f : A → Label) (terminal : A → Prop)
    (hterminal : ∀ l v S, terminal l → (stepAux (M l) v S).l = none)
    (hstep : ∀ l v S, ¬ terminal l →
      run (some (liftCfg f { l := some l, var := v, stk := S })) =
        (componentRun M
          (some { l := some l, var := v, stk := S })).map (liftCfg f))
    (n : Nat) (c d : Cfg TopGam A Sig)
    (hd : d.l ≠ none)
    (hrun : (componentRun M)^[n] (some c) = some d) :
    run^[n] (some (liftCfg f c)) = some (liftCfg f d) := by
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
              exact (inactive_no_active M (n + 1)
                { l := none, var := v, stk := S } d rfl hd hrun).elim
          | some l =>
              rw [Function.iterate_succ_apply] at hrun
              change (componentRun M)^[n]
                (some (stepAux (M l) v S)) = some d at hrun
              by_cases hbad : terminal l
              · have hnone := hterminal l v S hbad
                exact (inactive_no_active M n (stepAux (M l) v S)
                  d hnone hd hrun).elim
              · have hfirst := hstep l v S hbad
                have hrest := ih (stepAux (M l) v S) hrun
                rw [Function.iterate_succ_apply, hfirst]
                simpa [componentRun, step] using hrest

end ShiTMStageChain
