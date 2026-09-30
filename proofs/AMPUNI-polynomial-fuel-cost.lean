import «AMPUNI-polynomial-fuel-run»

set_option autoImplicit false
noncomputable section
namespace ShiTMPolynomialFuel
open Polynomial

/-- The coefficient of the initial counter size in the exact running time. -/
def workPoly : Nat → Polynomial ℕ
  | 0 => C 2 * X + C 3
  | r + 1 => C 3 * X + C 4 + (X + 1) * workPoly r

theorem work_eq (r n m : Nat) :
    work r n m = m * (workPoly r).eval n + 3 * r + 2 := by
  induction r generalizing m with
  | zero => simp [work, workPoly]
  | succ r ih =>
      simp only [work, workPoly, eval_add, eval_mul, eval_C, eval_X, eval_one]
      rw [ih]
      ring

/-- Both the fuel quantity and the time to construct it are polynomials. -/
def budgetPoly (d k : Nat) : Polynomial ℕ := C k * (X + 1) ^ (d + 1)
def fuelTimePoly (d k : Nat) : Polynomial ℕ := C k * workPoly d + C (3 * d + 3)

@[simp] theorem budgetPoly_eval (d k n : Nat) :
    (budgetPoly d k).eval n = k * (n + 1) ^ (d + 1) := by
  simp [budgetPoly]

@[simp] theorem fuelTimePoly_eval (d k n : Nat) :
    (fuelTimePoly d k).eval n = 1 + work d n k := by
  rw [work_eq]
  simp only [fuelTimePoly, eval_add, eval_mul, eval_C]
  omega

end ShiTMPolynomialFuel
