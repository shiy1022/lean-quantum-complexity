-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.product_family_orthonormal_three`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_product_family_orthonormal_three`. The real proof is on prove2.me.
import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

namespace ShiShallow

open ShiTensor

theorem product_family_orthonormal_three {m p q : ℕ}
    (u : Bits m → EuclideanSpace ℂ (Bits m)) (v : Bits p → EuclideanSpace ℂ (Bits p))
    (w : Bits q → EuclideanSpace ℂ (Bits q))
    (hu : Orthonormal ℂ u) (hv : Orthonormal ℂ v) (hw : Orthonormal ℂ w) :
    Orthonormal ℂ (fun i : (Bits m × Bits p) × Bits q =>
      (WithLp.toLp 2 (fun y : Bits (m + p + q) =>
          u i.1.1 (leftBits (leftBits y)) * v i.1.2 (rightBits (leftBits y))
            * w i.2 (rightBits y)) : EuclideanSpace ℂ (Bits (m + p + q)))) := by
  sorry

end ShiShallow
