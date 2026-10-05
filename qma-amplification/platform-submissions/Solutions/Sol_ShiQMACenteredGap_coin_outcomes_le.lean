import Definitions.Def_ShiQMACenteredGapScalarCentering
import Mathlib.Tactic
import Mathlib.Data.Real.Archimedean

set_option autoImplicit false

open ShiQMACenteredGap

theorem solution (q : Nat) (hq : 0 < q) :
    2 ^ coinBits q ≤ 8 * q := by
  have hlog := Nat.pow_log_le_self 2 (show 4 * q ≠ 0 by omega)
  dsimp [coinBits]
  rw [pow_succ]
  omega
