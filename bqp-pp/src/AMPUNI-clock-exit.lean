import «AMPUNI-typed-timeout-two-step»

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Turing Turing.TM2
namespace ShiTMClockExit
open ShiTMTypedTimeout
variable {K L sig : Type} [DecidableEq K] {Gam : K → Type}

/-- Replace every halt in a statement by a jump to a common cleanup entry. -/
def redirectHalt (exit : L) : Stmt Gam L sig → Stmt Gam L sig
  | .push k f q => .push k f (redirectHalt exit q)
  | .peek k f q => .peek k f (redirectHalt exit q)
  | .pop k f q => .pop k f (redirectHalt exit q)
  | .load f q => .load f (redirectHalt exit q)
  | .branch f q r => .branch f (redirectHalt exit q) (redirectHalt exit r)
  | .goto f => .goto f
  | .halt => .goto (fun _ => exit)

def finishCfg (exit : L) (c : Cfg Gam L sig) : Cfg Gam L sig :=
  { c with l := some (c.l.getD exit) }

theorem stepAux_redirectHalt (exit : L) (q : Stmt Gam L sig)
    (v : sig) (S : ∀ k, List (Gam k)) :
    stepAux (redirectHalt exit q) v S = finishCfg exit (stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | load f q ih => exact ih _ _
  | branch f q r ihq ihr =>
      simp only [redirectHalt, stepAux]
      cases h : f v
      · exact ihr _ _
      · exact ihq _ _
  | goto f => rfl
  | halt => rfl

/-- Both source halts and fuel exhaustion reach the same cleanup entry.
The caller supplies the cleanup statement at that entry. -/
def machine (M : L → Stmt Gam L sig)
    (onExit : Stmt (ClockGam Gam) (ClockL L) (sig × Bool)) :
    ClockL L → Stmt (ClockGam Gam) (ClockL L) (sig × Bool)
  | .inl p => redirectHalt timeout (clockMWith M .halt (.inl p))
  | .inr _ => onExit

def run (M : L → Stmt Gam L sig)
    (onExit : Stmt (ClockGam Gam) (ClockL L) (sig × Bool)) :=
  fun c : Option (Cfg (ClockGam Gam) (ClockL L) (sig × Bool)) =>
    c.bind (step (machine M onExit))

def cfg (fuel : List Bool) (c : Cfg Gam L sig) :=
  finishCfg timeout (liftCfg fuel c)

private theorem liftStk_fuel_cons (x : Bool) (fuel : List Bool)
    (S : ∀ k, List (Gam k)) :
    Function.update (liftStk fuel S) (Sum.inr ()) (x :: fuel) = liftStk (x :: fuel) S := by
  funext j
  cases j <;> simp [liftStk]

/-- One clocked source step consumes fuel and redirects a source halt to cleanup. -/
theorem two_steps (M : L → Stmt Gam L sig)
    (onExit : Stmt (ClockGam Gam) (ClockL L) (sig × Bool))
    (l : L) (v : sig) (S : ∀ k, List (Gam k)) (x : Bool) (fuel : List Bool) :
    (run M onExit)^[2] (some (cfg (x::fuel) ⟨some l, v, S⟩)) =
      some (cfg fuel (stepAux (M l) v S)) := by
  have hu : Function.update (liftStk (x::fuel) S) (Sum.inr ()) fuel = liftStk fuel S := by
    funext j
    cases j <;> simp [liftStk]
  have ht : run M onExit (some (cfg (x::fuel) ⟨some l, v, S⟩)) =
      some ⟨some (exec l), (v, true), liftStk fuel S⟩ := by
    simp [run, cfg, finishCfg, liftCfg, machine, clockMWith, tick,
      redirectHalt, step, stepAux, liftStk, hu, exec]
  rw [show (2 : Nat) = 1+1 by rfl, Function.iterate_add_apply]
  simp only [Function.iterate_one]
  rw [ht]
  change some (stepAux (redirectHalt timeout (clockStmt (M l))) (v, true) (liftStk fuel S)) = _
  rw [stepAux_redirectHalt, stepAux_clockStmt]
  rfl

theorem empty_fuel (M : L → Stmt Gam L sig)
    (onExit : Stmt (ClockGam Gam) (ClockL L) (sig × Bool))
    (l : L) (v : sig) (S : ∀ k, List (Gam k)) :
    run M onExit (some (cfg [] ⟨some l, v, S⟩)) =
      some ⟨some timeout, (v, false), liftStk [] S⟩ := by
  simp [run, cfg, finishCfg, liftCfg, machine, clockMWith, tick,
    redirectHalt, step, stepAux, liftStk, timeout]

end ShiTMClockExit
