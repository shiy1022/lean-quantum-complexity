import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace ShiQMAErrorIteration

/-- Failure probability of a majority of three independent trials. -/
def majorityError (e : ℝ) : ℝ := 3 * e ^ 2 - 2 * e ^ 3

/-- The scalar error recurrence, starting at the usual QMA error threshold. -/
noncomputable def error : Nat → ℝ
  | 0 => 1 / 3
  | r + 1 => majorityError (error r)

/-- A logarithmic number of rounds suffices for the target exponential error. -/
def roundsFor (m : Nat) : Nat := Nat.log 2 m + 4

end ShiQMAErrorIteration
