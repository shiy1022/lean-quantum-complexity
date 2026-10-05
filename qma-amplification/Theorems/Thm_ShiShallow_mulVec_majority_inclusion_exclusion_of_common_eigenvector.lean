-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.mulVec_majority_inclusion_exclusion_of_common_eigenvector`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_mulVec_majority_inclusion_exclusion_of_common_eigenvector`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem mulVec_majority_inclusion_exclusion_of_common_eigenvector {n : ℕ}
    (A B C : Op n) (φ : Bits n → ℂ) (α β γ : ℂ)
    (hA : Matrix.mulVec A φ = α • φ) (hB : Matrix.mulVec B φ = β • φ)
    (hC : Matrix.mulVec C φ = γ • φ) :
    Matrix.mulVec (A * B + B * C + C * A - (2 : ℂ) • (A * B * C)) φ
      = (α * β + β * γ + γ * α - 2 * (α * β * γ)) • φ := by
  sorry

end ShiShallow
