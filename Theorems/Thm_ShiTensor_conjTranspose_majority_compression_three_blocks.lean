-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTensor.conjTranspose_majority_compression_three_blocks`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTensor_conjTranspose_majority_compression_three_blocks`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix
import Definitions.Def_ShiTensor_Core
import Theorems.Thm_ShiTensor_sum_split_factor

set_option autoImplicit false

namespace ShiTensor

open ShiShallow ShiTensor

theorem conjTranspose_majority_compression_three_blocks {m w : ℕ}
    (W : Matrix (Bits m) (Bits w) ℂ)
    (hW : Matrix.conjTranspose W * W = (1 : Op w))
    (P : Op m) (A : Op w) (hA : A = Matrix.conjTranspose W * P * W)
    (Pi : Matrix (Bits (m + m + m)) (Bits (w + w + w)) ℂ)
    (hPi : Pi = Matrix.of fun (y : Bits (m + m + m)) (u : Bits (w + w + w)) =>
      W (leftBits (leftBits y)) (leftBits (leftBits u))
        * W (rightBits (leftBits y)) (rightBits (leftBits u))
        * W (rightBits y) (rightBits u))
    (P1 P2 P3 : Op (m + m + m))
    (hP1 : P1 = Matrix.of fun y z =>
      P (leftBits (leftBits y)) (leftBits (leftBits z))
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * (if rightBits y = rightBits z then 1 else 0))
    (hP2 : P2 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * P (rightBits (leftBits y)) (rightBits (leftBits z))
        * (if rightBits y = rightBits z then 1 else 0))
    (hP3 : P3 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * P (rightBits y) (rightBits z))
    (A1 A2 A3 : Op (w + w + w))
    (hA1 : A1 = Matrix.of fun y z =>
      A (leftBits (leftBits y)) (leftBits (leftBits z))
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * (if rightBits y = rightBits z then 1 else 0))
    (hA2 : A2 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * A (rightBits (leftBits y)) (rightBits (leftBits z))
        * (if rightBits y = rightBits z then 1 else 0))
    (hA3 : A3 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * A (rightBits y) (rightBits z)) :
    Matrix.conjTranspose Pi
        * (P1 * P2 + P2 * P3 + P3 * P1 - (2 : ℂ) • (P1 * P2 * P3)) * Pi
      = A1 * A2 + A2 * A3 + A3 * A1 - (2 : ℂ) • (A1 * A2 * A3) := by
  sorry

end ShiTensor
