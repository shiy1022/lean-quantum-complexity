import «AMPUNI-typed-timeout-step»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMTypedTimeout

private theorem liftStk_fuel_cons {K : Type} [DecidableEq K]
    {Gam : K → Type} (x : Bool) (fuel : List Bool)
    (S : ∀ k, List (Gam k)) :
    Function.update (liftStk (x :: fuel) S) (Sum.inr ()) fuel =
      liftStk fuel S := by
  funext j
  cases j <;> simp [liftStk]

/-- A clock tick consumes one Boolean fuel symbol; the following step
performs exactly one transition of the typed source machine. -/
theorem two_steps_simulate_one_with {K L sig : Type}
    [DecidableEq K] {Gam : K → Type}
    (M : L → Stmt Gam L sig)
    (onTimeout : Stmt (ClockGam Gam) (ClockL L) (sig × Bool))
    (l : L) (v : sig) (S : ∀ k, List (Gam k))
    (x : Bool) (fuel : List Bool) :
    (fun c : Option (Cfg (ClockGam Gam) (ClockL L) (sig × Bool)) =>
      c.bind (step (clockMWith M onTimeout)))^[2]
      (some (liftCfg (x :: fuel) { l := some l, var := v, stk := S })) =
      some (liftCfg fuel (stepAux (M l) v S)) := by
  rw [show (2 : Nat) = 1 + 1 by omega, Function.iterate_add_apply]
  simp only [Function.iterate_one, Option.bind_some]
  let ce : Cfg (ClockGam Gam) (ClockL L) (sig × Bool) :=
    { l := some (exec l)
      var := (v, true)
      stk := liftStk fuel S }
  have htick : step (clockMWith M onTimeout)
      (liftCfg (x :: fuel) { l := some l, var := v, stk := S }) =
      some ce := by
    simp [ce, liftCfg, step, clockMWith, tick, exec,
      liftStk, liftStk_fuel_cons]
  rw [htick]
  change step (clockMWith M onTimeout) ce = _
  unfold ce
  simp only [step, clockMWith, exec]
  rw [stepAux_clockStmt]

end ShiTMTypedTimeout
