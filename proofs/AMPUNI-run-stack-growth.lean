import «AMPUNI-subroutine-lift»

set_option autoImplicit false
open Turing Turing.TM2
namespace ShiTMStackGrowth
variable {K L V : Type} [DecidableEq K] [Fintype K] {G : K → Type}

def size (S : ∀ k, List (G k)) : Nat := ∑ k, (S k).length

def potential : Option (Cfg G L V) → Nat
  | none => 0
  | some c => size c.stk

/-- Lift a one-step stack-growth bound to every bounded execution, including
runs that halt early. No validity assumption about the input is needed. -/
theorem potential_run_le (M : L → Stmt G L V) (C : Nat)
    (hstep : ∀ l v S, size (stepAux (M l) v S).stk ≤ size S+C)
    (n : Nat) (c : Option (Cfg G L V)) :
    potential ((ShiTMSubroutine.run M)^[n] c) ≤ potential c+n*C := by
  have hone : ∀ x, potential (ShiTMSubroutine.run M x) ≤ potential x+C := by
    intro x
    cases x with
    | none => simp [ShiTMSubroutine.run, potential]
    | some x =>
        rcases x with ⟨l, v, S⟩
        cases l with
        | none => simp [ShiTMSubroutine.run, step, potential]
        | some l => exact hstep l v S
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      have hr := ih (ShiTMSubroutine.run M c)
      have hs := hone c
      simp only [Nat.succ_mul, Nat.add_mul, Nat.one_mul]
      omega

theorem run_size_le (M : L → Stmt G L V) (C : Nat)
    (hstep : ∀ l v S, size (stepAux (M l) v S).stk ≤ size S+C)
    (n : Nat) (c d : Cfg G L V)
    (hr : (ShiTMSubroutine.run M)^[n] (some c) = some d) :
    size d.stk ≤ size c.stk+n*C := by
  have h := potential_run_le M C hstep n (some c)
  rw [hr] at h
  exact h

end ShiTMStackGrowth
