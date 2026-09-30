-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTensor.sum_normSq_tensor_three`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTensor_sum_normSq_tensor_three`. The real proof is on prove2.me.
import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

namespace ShiTensor

open ShiShallow

theorem sum_normSq_tensor_three {m p q : ℕ} (ψ : QState m) (φ : QState p) (χ : QState q)
    (hψ : ∑ a : Bits m, ‖ψ a‖ ^ 2 = 1)
    (hφ : ∑ b : Bits p, ‖φ b‖ ^ 2 = 1)
    (hχ : ∑ c : Bits q, ‖χ c‖ ^ 2 = 1) :
    ∑ y : Bits (m + p + q), ‖tensor (tensor ψ φ) χ y‖ ^ 2 = 1 := by
  sorry

end ShiTensor
