import Definitions.Def_ShiQMACenteredGap

set_option autoImplicit false
open ShiQMAErrorIteration ShiQMACenteredGap

/-- The logarithmic normalization schedule uses at most polynomially many copies. -/
theorem solution (q : Nat) (hq : 0 < q) :
    3 ^ gapRounds q ≤ 27 * q ^ 5 := by
  have hlog := Nat.pow_log_le_self 2 (Nat.ne_of_gt hq)
  have hp : 27 ^ Nat.log 2 q ≤ 32 ^ Nat.log 2 q :=
    Nat.pow_le_pow_left (by decide) _
  have heq : 32 ^ Nat.log 2 q = (2 ^ Nat.log 2 q) ^ 5 := by
    rw [← pow_mul, Nat.mul_comm]
    exact (pow_mul 2 5 (Nat.log 2 q)).symm
  rw [heq] at hp
  have hs := hp.trans (Nat.pow_le_pow_left hlog 5)
  dsimp [gapRounds]
  rw [pow_mul, show (3 : Nat) ^ 3 = 27 by norm_num, pow_succ]
  nlinarith
