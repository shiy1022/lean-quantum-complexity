-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.product_family_parseval_three`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_product_family_parseval_three`. The real proof is on prove2.me.
import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

namespace ShiShallow

open ShiTensor

theorem product_family_parseval_three {m p q : ℕ}
    (V : (Bits m × Bits p) × Bits q → EuclideanSpace ℂ (Bits (m + p + q)))
    (hV : Orthonormal ℂ V) (x : EuclideanSpace ℂ (Bits (m + p + q))) :
    ∑ i : (Bits m × Bits p) × Bits q, ‖inner ℂ x (V i)‖ ^ 2 = ‖x‖ ^ 2 := by
  sorry

end ShiShallow
