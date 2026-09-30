-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTensor.mulVec_block_extend_right_tensor_eigenvector`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTensor_mulVec_block_extend_right_tensor_eigenvector`. The real proof is on prove2.me.
import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiShallow_Matrix
import Theorems.Thm_ShiTensor_sum_split_factor

set_option autoImplicit false

namespace ShiTensor

open ShiShallow ShiTensor

theorem mulVec_block_extend_right_tensor_eigenvector {m p : ℕ} (A : Op p) (α : ℂ)
    (u : Bits m → ℂ) (v : Bits p → ℂ)
    (hv : ∀ b' : Bits p, ∑ b : Bits p, A b' b * v b = α * v b') :
    Matrix.mulVec
        (Matrix.of fun y z : Bits (m + p) =>
          if leftBits y = leftBits z then A (rightBits y) (rightBits z) else 0)
        (fun y => u (leftBits y) * v (rightBits y))
      = fun y => α * (u (leftBits y) * v (rightBits y)) := by
  sorry

end ShiTensor
