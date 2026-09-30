import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace ShiTMFanout

/-- Uniform quadratic bound for the emitted block when the count is at
most the retained-input length and the target base is at most three times
that length. The two amplifier fanouts both satisfy these inequalities. -/
theorem fanout_cost_le (n b L : Nat) (hn : n ≤ L) (hb : b ≤ 3*L)
    (hL : 1 ≤ L) :
    2*n*n + n*(2*b+7) + 4 ≤ 19*L*L := by
  have hn2 := Nat.mul_le_mul hn hn
  have hnb := Nat.mul_le_mul hn hb
  have hLL : L ≤ L*L := by
    simpa using Nat.mul_le_mul_left L hL
  have h1 : 1 ≤ L*L := le_trans hL hLL
  nlinarith

end ShiTMFanout
