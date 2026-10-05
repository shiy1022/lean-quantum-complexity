import «AMPUNI-cleanup-terminal»
import «AMPUNI-clocked-cleanup-machine»
import «AMPUNI-subroutine-full-lift»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
noncomputable section

namespace ShiTMRepeatClocked
open ShiTMTypedTimeout
variable {K L sig : Type} [DecidableEq K] [Fintype K] {Gam : K → Type}
variable (output : K) (initial : sig)

abbrev Label := ClockL L ⊕
  (ShiTMGenericCleanup.PC (Sum.inl output : ClockK K) ⊕ Unit)

def machine (M : L → Stmt Gam L sig) :
    Label (L := L) output →
      Stmt (ClockGam Gam) (Label (L := L) output) (sig × Bool)
  | .inl (.inr _) => .goto (fun _ => .inr (.inl 0))
  | .inl (.inl p) =>
      ShiTMSubroutine.stmt Sum.inl (ShiTMClockExit.machine M .halt (.inl p))
  | .inr pc =>
      ShiTMSubroutine.stmt Sum.inr
        (ShiTMRepeatCleanup.handoffMachine (Sum.inl output) initial pc)

def run (M : L → Stmt Gam L sig) :=
  ShiTMSubroutine.run (machine output initial M)

def startCfg (fuel : List Bool) (c : Cfg Gam L sig) :
    Cfg (ClockGam Gam) (Label (L := L) output) (sig × Bool) :=
  ShiTMSubroutine.cfg Sum.inl (ShiTMClockExit.cfg fuel c)

def activeFinish (ys : List (Gam output)) :
    Cfg (ClockGam Gam) (Label (L := L) output) (sig × Bool) :=
  ⟨some (.inr (.inr ())), (initial, false),
    Function.update (fun _ => []) (.inl output) ys⟩

theorem clock_run (M : L → Stmt Gam L sig) (fuel : List Bool)
    (c : Cfg Gam L sig) (steps : Nat) (v : sig)
    (S : ∀ k, List (ClockGam Gam k))
    (hr : (ShiTMClockExit.run M .halt)^[steps]
      (some (ShiTMClockExit.cfg fuel c)) =
        some ⟨some timeout, (v, false), S⟩) :
    (run output initial M)^[steps]
      (some (startCfg output fuel c)) =
        some ⟨some (.inl timeout), (v, false), S⟩ := by
  exact ShiTMSubroutine.run_to_terminal (ShiTMClockExit.machine M .halt)
    (machine output initial M) Sum.inl timeout rfl
    (by intro l hl
        cases l with
        | inl p => rfl
        | inr u => cases u; exact (hl rfl).elim)
    steps _ _ rfl hr

theorem exit_step (M : L → Stmt Gam L sig) (v : sig × Bool)
    (S : ∀ k, List (ClockGam Gam k)) :
    (run output initial M)^[1]
      (some ⟨some (.inl timeout), v, S⟩) =
        some ⟨some (.inr (.inl 0)), v, S⟩ := rfl

/-- Clock cleanup now preserves its output at an active handoff label. -/
theorem cleanup_run (M : L → Stmt Gam L sig) (v : sig × Bool)
    (S : ∀ k, List (ClockGam Gam k)) :
    (run output initial M)^[
      ShiTMGenericCleanup.suffixCost
        (ShiTMGenericCleanup.todo (Sum.inl output : ClockK K)) S + 1]
      (some ⟨some (.inr (.inl 0)), v, S⟩) =
        some (activeFinish output initial (S (.inl output))) := by
  have h := ShiTMSubroutine.run_iter_lift
    (ShiTMRepeatCleanup.handoffMachine
      (Sum.inl output : ClockK K) initial)
    (machine output initial M) Sum.inr (by intro l; rfl)
    (ShiTMGenericCleanup.suffixCost
      (ShiTMGenericCleanup.todo (Sum.inl output : ClockK K)) S + 1)
    (some ⟨some (.inl 0), v, S⟩)
  have hc := ShiTMRepeatCleanup.handoff_cleanup_run
    (Sum.inl output : ClockK K) initial v S
  change (ShiTMSubroutine.run _)^[_] _ = _ at hc
  rw [hc] at h
  exact h

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- With any finite fuel, the clocked one-round body exits at an active handoff. -/
theorem total_from_fuel (M : L → Stmt Gam L sig)
    (fuel : List Bool) (c : Cfg Gam L sig) :
    ∃ (steps : Nat) (ys : List (Gam output)),
      (run output initial M)^[steps]
        (some (startCfg output fuel c)) =
          some (activeFinish output initial ys) := by
  obtain ⟨t, rest, v, S, hr, _, _⟩ :=
    ShiTMClockExit.reaches_exit M .halt fuel c
  have h0 := clock_run output initial M fuel c t v
    (liftStk rest S) hr
  have h1 := iterTwo (run output initial M) _ _ _ _ _ h0
    (exit_step output initial M (v, false) (liftStk rest S))
  have h2 := iterTwo (run output initial M) _ _ _ _ _ h1
    (cleanup_run output initial M (v, false) (liftStk rest S))
  exact ⟨_, S output, h2⟩

/-- A successful original body run retains the same output at the active handoff. -/
theorem preserves_exact_run (M : L → Stmt Gam L sig) (steps : Nat)
    (c : Cfg Gam L sig) (v : sig)
    (S : ∀ k, List (Gam k)) (rest : List Bool)
    (hr : (ShiTMSubroutine.run M)^[steps] (some c) =
      some ⟨none, v, S⟩) :
    (run output initial M)^[
      2 * steps + 1 +
        (ShiTMGenericCleanup.suffixCost
          (ShiTMGenericCleanup.todo (Sum.inl output : ClockK K))
          (liftStk rest S) + 1)]
      (some (startCfg output (List.replicate steps true ++ rest) c)) =
        some (activeFinish output initial (S output)) := by
  have hc := ShiTMClockExit.exact_run M .halt
    steps c ⟨none, v, S⟩ rest hr
  have h0 := clock_run output initial M
    (List.replicate steps true ++ rest) c (2 * steps)
    v (liftStk rest S) hc
  have h1 := iterTwo (run output initial M) _ _ _ _ _ h0
    (exit_step output initial M (v, false) (liftStk rest S))
  exact iterTwo (run output initial M) _ _ _ _ _ h1
    (cleanup_run output initial M (v, false) (liftStk rest S))

end ShiTMRepeatClocked
