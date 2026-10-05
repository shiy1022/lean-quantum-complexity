import Mathlib

/-! Q00 harness smoke test: a tiny Mathlib-importing module with one audited theorem. -/

namespace ShiQIP

theorem smoke_two_mul (x : ℝ) : 2 * x = x + x := by ring

end ShiQIP
