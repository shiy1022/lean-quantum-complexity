import ReversibleSymbolicCellBinding
import ReversibleIndexExpressionClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

theorem cellAddressBindingSteps_formula (input capacity index target : R) (offset rank stride : Nat)
    (hbt : input ≠ target) (hct : capacity ≠ target) (hit : index ≠ target) (cs : R → Nat) :
    cellAddressBindingSteps input capacity index target offset rank stride cs =
      (2 * cs target + 1) +
        (((7 * cs input + 2) + offset) + (rank * stride) * (7 * cs capacity + 2) +
          stride * (7 * cs index + 2)) + (2 * cs index + 1) := by
  simp [cellAddressBindingSteps, cellAddressAtoms_steps _ _ _ _ _ _ _ hct hit, hbt, hct, hit]

theorem symbolicCellBindingSteps_polynomial (p : TickIndexExpr) (input capacity position index target : R)
    (offset rank stride : Nat) (hbi : input ≠ index) (hci : capacity ≠ index)
    (hbt : input ≠ target) (hct : capacity ≠ target) (hit : index ≠ target) (bound : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : R → Nat),
      (∀ r, cs r ≤ bound.eval n) →
      symbolicCellBindingSteps p input capacity position index target offset rank stride cs ≤ clock.eval n := by
  obtain ⟨exprClock, he⟩ := indexExpressionSteps_polynomial p capacity position index bound bound bound
  let qBound := Polynomial.C 2 * bound + Polynomial.C p.allowance
  let arithClock := ((Polynomial.C 7 * bound + Polynomial.C 2) + Polynomial.C offset) +
    Polynomial.C (rank * stride) * (Polynomial.C 7 * bound + Polynomial.C 2) +
    Polynomial.C stride * (Polynomial.C 7 * qBound + Polynomial.C 2)
  refine ⟨exprClock + ((Polynomial.C 2 * bound + Polynomial.C 1) + arithClock +
    (Polynomial.C 2 * qBound + Polynomial.C 1)), ?_⟩
  intro n cs hb
  have h₁ := he n cs (hb capacity) (hb position) (hb index)
  have hq : p.eval (cs capacity) (cs position) ≤ 2 * bound.eval n + p.allowance := by
    have h := p.eval_bound (cs capacity) (cs position)
    have hc := hb capacity
    have hi := hb position
    omega
  have hcap := Nat.mul_le_mul_left (rank * stride)
    (show 7 * cs capacity + 2 ≤ 7 * bound.eval n + 2 by have h := hb capacity; omega)
  have hidx := Nat.mul_le_mul_left stride
    (show 7 * p.eval (cs capacity) (cs position) + 2 ≤
      7 * (2 * bound.eval n + p.allowance) + 2 by omega)
  rw [symbolicCellBindingSteps, cellAddressBindingSteps_formula _ _ _ _ _ _ _ hbt hct hit]
  simp only [Function.update_self, Function.update_of_ne hbi, Function.update_of_ne hci,
    Function.update_of_ne (Ne.symm hit), qBound, arithClock, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C]
  have hin := hb input
  have htarget := hb target
  omega

end ShiReversibleGenerator
