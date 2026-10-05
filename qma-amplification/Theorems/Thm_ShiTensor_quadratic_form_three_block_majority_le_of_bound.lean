-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTensor.quadratic_form_three_block_majority_le_of_bound`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTensor_quadratic_form_three_block_majority_le_of_bound`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix
import Definitions.Def_ShiTensor_Core
import Theorems.Thm_ShiShallow_exists_sum_form_eigenbasis
import Theorems.Thm_ShiShallow_eigenvalues_nonneg_of_quadratic_form_nonneg
import Theorems.Thm_ShiShallow_eigenvalues_le_of_quadratic_form_le
import Theorems.Thm_ShiShallow_product_eigenbasis_sum_form_three
import Theorems.Thm_ShiShallow_mulVec_majority_inclusion_exclusion_of_common_eigenvector
import Theorems.Thm_ShiShallow_quadratic_form_majority_le_of_eigenbasis

set_option autoImplicit false

namespace ShiTensor

open ShiShallow ShiTensor

theorem quadratic_form_three_block_majority_le_of_bound {w : ℕ} (A : Op w) (hA : A.IsHermitian) (s : ℝ) (hs : s ≤ 1)
    (hqf : ∀ v : Bits w → ℂ, (∑ y : Bits w, ‖v y‖ ^ 2) = 1 →
      0 ≤ (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re
        ∧ (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec A v y).re ≤ s)
    (A1 A2 A3 : Op (w + w + w))
    (hlift : ∀ (p q t : QState w) (α β γ : ℂ),
      Matrix.mulVec A p = α • p → Matrix.mulVec A q = β • q → Matrix.mulVec A t = γ • t →
        Matrix.mulVec A1 (tensor (tensor p q) t) = α • tensor (tensor p q) t
          ∧ Matrix.mulVec A2 (tensor (tensor p q) t) = β • tensor (tensor p q) t
          ∧ Matrix.mulVec A3 (tensor (tensor p q) t) = γ • tensor (tensor p q) t)
    (Θ : QState (w + w + w)) (hΘ : (∑ y : Bits (w + w + w), ‖Θ y‖ ^ 2) = 1) :
    (∑ y : Bits (w + w + w), (starRingEnd ℂ) (Θ y)
        * Matrix.mulVec (A1 * A2 + A2 * A3 + A3 * A1 - (2 : ℂ) • (A1 * A2 * A3)) Θ y).re
      ≤ 3 * s ^ 2 - 2 * s ^ 3 := by
  sorry

end ShiTensor
