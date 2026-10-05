import «AMPUNI-finite-stack-growth»
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Turing Turing.TM2
namespace ShiTMStackGrowth
variable {K L V : Type} [DecidableEq K] [Fintype K] {G : K → Type}

/-- Charge both elapsed time and the final stack size to the initial size.
The reserve P is carried unchanged between stages. -/
theorem run_charge_le (M : L → Stmt G L V) (C : Nat)
    (hg : ∀ l v S, size (stepAux (M l) v S).stk ≤ size S+C)
    (t : Nat) (c d : Cfg G L V) (P A : Nat)
    (hr : (ShiTMSubroutine.run M)^[t] (some c) = some d)
    (ht : t ≤ A*(size c.stk+P)) :
    t+size d.stk+P ≤ (1+A*(C+1))*(size c.stk+P) := by
  have hs := run_size_le M C hg t c d hr
  have hm := Nat.mul_le_mul_right (C+1) ht
  nlinarith

/-- Sequential composition preserves a linear charge in the same reserve. -/
theorem charge_comp {t u s₀ s₁ s₂ P A B : Nat}
    (h₁ : t+s₁+P ≤ A*(s₀+P))
    (h₂ : u+s₂+P ≤ B*(s₁+P)) (hB : 1 ≤ B) :
    (t+u)+s₂+P ≤ (B*A)*(s₀+P) := by
  have hm := Nat.mul_le_mul_left B h₁
  have ht : t ≤ B*t := by nlinarith
  nlinarith

/-- A larger common reserve can be used without changing the coefficient. -/
theorem charge_reserve_mono {t s₀ s₁ P Q A : Nat}
    (h : t+s₁+P ≤ A*(s₀+P)) (hA : 1 ≤ A) (hPQ : P ≤ Q) :
    t+s₁+Q ≤ A*(s₀+Q) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hPQ
  have hd : d ≤ A*d := by nlinarith
  nlinarith

end ShiTMStackGrowth
