import Definitions.Def_ShiQMAErrorIteration
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace ShiQMACenteredGap
open ShiQMAErrorIteration

/-- Majority of three acts on displacement from acceptance probability one half. -/
noncomputable def biasStep (d : ℝ) : ℝ := 3 / 2 * d - 2 * d ^ 3

noncomputable def biasIter (d : ℝ) : Nat → ℝ
  | 0 => d
  | r + 1 => biasStep (biasIter d r)

/-- A concrete logarithmic schedule for a bias at least 1/(6q). -/
def gapRounds (q : Nat) : Nat := 3 * (Nat.log 2 q + 1)

end ShiQMACenteredGap
