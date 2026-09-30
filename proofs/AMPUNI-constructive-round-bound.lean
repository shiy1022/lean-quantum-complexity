import «AMPUNI-constructive-schedule»

set_option autoImplicit false

namespace ShiQMAConstructiveSchedule
open Polynomial

/-- The computable logarithmic schedule is bounded by a linear polynomial
in the input length, which is enough for charging all controller rounds. -/
theorem rounds_le_linear (p : Polynomial ℕ) (n : Nat) :
    rounds p n ≤
      p.natDegree * n +
        (Nat.log 2 (p.eval 1 + 1) + 2 * p.natDegree + 4) := by
  have hlog := Nat.log_le_self 2 (n + 1)
  have hmul : p.natDegree * (Nat.log 2 (n + 1) + 1) ≤
      p.natDegree * n + 2 * p.natDegree := by
    calc
      _ ≤ p.natDegree * (n + 2) :=
        Nat.mul_le_mul_left p.natDegree (by omega)
      _ = p.natDegree * n + 2 * p.natDegree := by ring
  dsimp [rounds, exponentBudget]
  omega

theorem rounds_polyBounded (p : Polynomial ℕ) :
    ∃ R : Polynomial ℕ,
      ∀ n : Nat, rounds p n ≤ R.eval n := by
  let R : Polynomial ℕ := C p.natDegree * X +
    C (Nat.log 2 (p.eval 1 + 1) + 2 * p.natDegree + 4)
  refine ⟨R, ?_⟩
  intro n
  simpa [R, eval_add, eval_mul, eval_C, eval_X] using
    rounds_le_linear p n

end ShiQMAConstructiveSchedule
