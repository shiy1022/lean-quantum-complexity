import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Nat.Log

set_option autoImplicit false

namespace ShiQMACenteredGap

/-- The probability of the auxiliary coin used in affine acceptance centering. -/
noncomputable def centeringCoin (a b : ℝ) : ℝ := 1 - (a + b) / 2

/-- Run the verifier with probability one half, otherwise use the auxiliary coin.
This definition is scalar arithmetic, not yet a circuit implementation. -/
noncomputable def centeredAcceptance (u t : ℝ) : ℝ := (t + u) / 2

/-- Only logarithmically many fair bits are needed at inverse-polynomial gap. -/
def coinBits (q : Nat) : Nat := Nat.log 2 (4 * q) + 1

end ShiQMACenteredGap
