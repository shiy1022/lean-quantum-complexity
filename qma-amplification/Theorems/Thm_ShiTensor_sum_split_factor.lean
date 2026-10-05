-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTensor.sum_split_factor`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTensor_sum_split_factor`. The real proof is on prove2.me.
import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

open ShiShallow

namespace ShiTensor

theorem sum_split_factor {m p : ℕ} {R : Type*} [NonUnitalNonAssocSemiring R]
    (f : Bits m → R) (g : Bits p → R) :
    ∑ y : Bits (m + p), f (leftBits y) * g (rightBits y)
      = (∑ a : Bits m, f a) * ∑ b : Bits p, g b := by
  sorry

end ShiTensor
