-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTensor.mulVec_block_extend_tensor_eigenvector`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTensor_mulVec_block_extend_tensor_eigenvector`. The real proof is on prove2.me.
import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiTensor

open ShiShallow

theorem mulVec_block_extend_tensor_eigenvector {m p : ℕ} (A : Op m) (α : ℂ)
    (u : Bits m → ℂ) (v : Bits p → ℂ)
    (hu : ∀ a' : Bits m, ∑ a : Bits m, A a' a * u a = α * u a') :
    Matrix.mulVec
        (Matrix.of fun y z : Bits (m + p) =>
          if rightBits y = rightBits z then A (leftBits y) (leftBits z) else 0)
        (fun y => u (leftBits y) * v (rightBits y))
      = fun y => α * (u (leftBits y) * v (rightBits y)) := by
  sorry

end ShiTensor
