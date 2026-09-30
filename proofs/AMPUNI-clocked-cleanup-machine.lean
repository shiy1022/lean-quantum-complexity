import «AMPUNI-clock-exit-bounds»
import «AMPUNI-generic-clock-cleanup»
import «AMPUNI-subroutine-full-lift»
import «AMPUNI-finite-stack-growth»
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
noncomputable section
namespace ShiTMClockedCleanup
open ShiTMTypedTimeout
variable {K L sig : Type} [DecidableEq K] [Fintype K] {Gam : K → Type}
variable (output : K) (initial : sig)

abbrev Label := ClockL L ⊕ ShiTMGenericCleanup.PC (Sum.inl output : ClockK K)

def machine (M : L → Stmt Gam L sig) :
    Label (L := L) output → Stmt (ClockGam Gam) (Label (L := L) output) (sig × Bool)
  | .inl (.inr _) => .goto (fun _ => .inr 0)
  | .inl (.inl p) => ShiTMSubroutine.stmt Sum.inl (ShiTMClockExit.machine M .halt (.inl p))
  | .inr pc => ShiTMSubroutine.stmt Sum.inr
      (ShiTMGenericCleanup.machine (Sum.inl output : ClockK K) initial pc)

def run (M : L → Stmt Gam L sig) := ShiTMSubroutine.run (machine output initial M)

def startCfg (fuel : List Bool) (c : Cfg Gam L sig) :
    Cfg (ClockGam Gam) (Label (L := L) output) (sig × Bool) :=
  ShiTMSubroutine.cfg Sum.inl (ShiTMClockExit.cfg fuel c)

def haltCfg (ys : List (Gam output)) :
    Cfg (ClockGam Gam) (Label (L := L) output) (sig × Bool) :=
  ⟨none, (initial, false), Function.update (fun _ => []) (.inl output) ys⟩

theorem clock_run (M : L → Stmt Gam L sig) (fuel : List Bool) (c : Cfg Gam L sig)
    (steps : Nat) (v : sig) (S : ∀ k, List (ClockGam Gam k))
    (hr : (ShiTMClockExit.run M .halt)^[steps] (some (ShiTMClockExit.cfg fuel c)) =
      some ⟨some timeout, (v, false), S⟩) :
    (run output initial M)^[steps] (some (startCfg output fuel c)) =
      some ⟨some (.inl timeout), (v, false), S⟩ := by
  exact ShiTMSubroutine.run_to_terminal (ShiTMClockExit.machine M .halt)
    (machine output initial M) Sum.inl timeout rfl
    (by intro l hl; cases l with
        | inl p => rfl
        | inr u => cases u; exact (hl rfl).elim)
    steps _ _ rfl hr

theorem exit_step (M : L → Stmt Gam L sig) (v : sig × Bool)
    (S : ∀ k, List (ClockGam Gam k)) :
    (run output initial M)^[1] (some ⟨some (.inl timeout), v, S⟩) =
      some ⟨some (.inr 0), v, S⟩ := rfl

theorem cleanup_run (M : L → Stmt Gam L sig) (v : sig × Bool)
    (S : ∀ k, List (ClockGam Gam k)) :
    (run output initial M)^[ShiTMGenericCleanup.suffixCost
        (ShiTMGenericCleanup.todo (Sum.inl output : ClockK K)) S+1]
      (some ⟨some (.inr 0), v, S⟩) =
        some (haltCfg (L := L) output initial (S (.inl output))) := by
  have h := ShiTMSubroutine.run_iter_lift
    (ShiTMGenericCleanup.machine (Sum.inl output : ClockK K) initial)
    (machine output initial M) Sum.inr (by intro l; rfl)
    (ShiTMGenericCleanup.suffixCost (ShiTMGenericCleanup.todo (Sum.inl output : ClockK K)) S+1)
    (some ⟨some 0, v, S⟩)
  have hc := ShiTMGenericCleanup.cleanup_run (Sum.inl output : ClockK K) initial v S
  change (ShiTMSubroutine.run _)^[_] _ = _ at hc
  rw [hc] at h
  exact h

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a+b] x = z := by
  rw [show a+b = b+a by omega, Function.iterate_add_apply, hxy, hyz]

/-- For every input state and every finite fuel supply, the clocked controller
halts in canonical form. No source validity or source termination is assumed. -/
theorem total_from_fuel (M : L → Stmt Gam L sig) (fuel : List Bool) (c : Cfg Gam L sig) :
    ∃ (steps : Nat) (ys : List (Gam output)),
      (run output initial M)^[steps] (some (startCfg output fuel c)) =
        some (haltCfg (L := L) output initial ys) := by
  obtain ⟨t, rest, v, S, hr, _, _⟩ := ShiTMClockExit.reaches_exit M .halt fuel c
  have h0 := clock_run output initial M fuel c t v (liftStk rest S) hr
  have h1 := iterTwo (run output initial M) _ _ _ _ _ h0
    (exit_step output initial M (v, false) (liftStk rest S))
  have h2 := iterTwo (run output initial M) _ _ _ _ _ h1
    (cleanup_run output initial M (v, false) (liftStk rest S))
  exact ⟨_, S output, h2⟩

/-- A successful source computation keeps its output through clock exit and cleanup. -/
theorem preserves_exact_run (M : L → Stmt Gam L sig) (steps : Nat)
    (c : Cfg Gam L sig) (v : sig) (S : ∀ k, List (Gam k)) (rest : List Bool)
    (hr : (ShiTMSubroutine.run M)^[steps] (some c) = some ⟨none, v, S⟩) :
    (run output initial M)^[2*steps+1+
        (ShiTMGenericCleanup.suffixCost
          (ShiTMGenericCleanup.todo (Sum.inl output : ClockK K)) (liftStk rest S)+1)]
      (some (startCfg output (List.replicate steps true ++ rest) c)) =
        some (haltCfg (L := L) output initial (S output)) := by
  have hc := ShiTMClockExit.exact_run M .halt steps c ⟨none, v, S⟩ rest hr
  have h0 := clock_run output initial M (List.replicate steps true ++ rest) c
    (2*steps) v (liftStk rest S) hc
  have h1 := iterTwo (run output initial M) _ _ _ _ _ h0
    (exit_step output initial M (v, false) (liftStk rest S))
  exact iterTwo (run output initial M) _ _ _ _ _ h1
    (cleanup_run output initial M (v, false) (liftStk rest S))

theorem liftStk_size (fuel : List Bool) (S : ∀ k, List (Gam k)) :
    ShiTMStackGrowth.size (liftStk fuel S) = ShiTMStackGrowth.size S+fuel.length := by
  simp [ShiTMStackGrowth.size, liftStk, Fintype.sum_sum_type]

/-- The all-input bound depends only on supplied fuel and initial stored data.
The coefficient is fixed by the finite controller, not by the source input. -/
theorem total_from_fuel_bounded [Fintype L] (M : L → Stmt Gam L sig) :
    ∃ C : Nat, ∀ (fuel : List Bool) (c : Cfg Gam L sig),
      ∃ (steps : Nat) (ys : List (Gam output)),
        (run output initial M)^[steps] (some (startCfg output fuel c)) =
          some (haltCfg (L := L) output initial ys) ∧
        steps ≤ (C+1)*(2*fuel.length+1)+ShiTMStackGrowth.size c.stk+
          fuel.length+Fintype.card (ClockK K)+2 := by
  obtain ⟨C, hg⟩ := ShiTMStackGrowth.finite_growth (machine output initial M)
  refine ⟨C, ?_⟩
  intro fuel c
  obtain ⟨t, rest, v, S, hr, ht, _⟩ := ShiTMClockExit.reaches_exit M .halt fuel c
  have h0 := clock_run output initial M fuel c t v (liftStk rest S) hr
  have hs := ShiTMStackGrowth.run_size_le (machine output initial M) C hg
    t _ _ h0
  change ShiTMStackGrowth.size (liftStk rest S) ≤
    ShiTMStackGrowth.size (liftStk fuel c.stk)+t*C at hs
  rw [liftStk_size fuel c.stk] at hs
  have hc := ShiTMGenericCleanup.cleanup_cost_le
    (Sum.inl output : ClockK K) (liftStk rest S)
  have hm := Nat.mul_le_mul_left (C+1) ht
  have h1 := iterTwo (run output initial M) _ _ _ _ _ h0
    (exit_step output initial M (v, false) (liftStk rest S))
  have h2 := iterTwo (run output initial M) _ _ _ _ _ h1
    (cleanup_run output initial M (v, false) (liftStk rest S))
  refine ⟨_, S output, h2, ?_⟩
  nlinarith

/-- A budget at least as large as a successful source run preserves the
source output, with linear overhead in that budget and initial data. -/
theorem preserves_bounded_run [Fintype L] (M : L → Stmt Gam L sig) :
    ∃ C : Nat, ∀ (budget steps : Nat) (c : Cfg Gam L sig) (v : sig)
      (S : ∀ k, List (Gam k)),
      (ShiTMSubroutine.run M)^[steps] (some c) = some ⟨none, v, S⟩ →
      steps ≤ budget →
      ∃ t : Nat,
        (run output initial M)^[t]
          (some (startCfg output (List.replicate budget true) c)) =
            some (haltCfg (L := L) output initial (S output)) ∧
        t ≤ (C+3)*budget+ShiTMStackGrowth.size c.stk+Fintype.card (ClockK K)+2 := by
  obtain ⟨C, hg⟩ := ShiTMStackGrowth.finite_growth M
  refine ⟨C, ?_⟩
  intro budget steps c v S hr hb
  have hs := ShiTMStackGrowth.run_size_le M C hg steps c ⟨none, v, S⟩ hr
  change ShiTMStackGrowth.size S ≤ ShiTMStackGrowth.size c.stk+steps*C at hs
  have hrep : List.replicate budget true =
      List.replicate steps true ++ List.replicate (budget-steps) true := by
    rw [← List.replicate_add]
    congr 1
    omega
  have hrun := preserves_exact_run output initial M steps c v S
    (List.replicate (budget-steps) true) hr
  rw [← hrep] at hrun
  have hc := ShiTMGenericCleanup.cleanup_cost_le (Sum.inl output : ClockK K)
    (liftStk (List.replicate (budget-steps) true) S)
  rw [liftStk_size, List.length_replicate] at hc
  have hm := Nat.mul_le_mul_left C hb
  have hrest := Nat.sub_le budget steps
  exact ⟨_, hrun, by nlinarith⟩

end ShiTMClockedCleanup
