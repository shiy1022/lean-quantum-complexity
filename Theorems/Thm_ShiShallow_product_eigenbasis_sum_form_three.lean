-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.product_eigenbasis_sum_form_three`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_product_eigenbasis_sum_form_three`. The real proof is on prove2.me.
import Definitions.Def_ShiTensor_Core
import Theorems.Thm_ShiShallow_product_family_orthonormal_three
import Theorems.Thm_ShiShallow_product_family_parseval_three

set_option autoImplicit false

namespace ShiShallow

open ShiTensor

theorem product_eigenbasis_sum_form_three {M : ℕ} (u : Bits M → (Bits M → ℂ))
    (horth : ∀ i j, (∑ y : Bits M, (starRingEnd ℂ) (u i y) * u j y) = if i = j then 1 else 0) :
    (∀ i j : (Bits M × Bits M) × Bits M,
        (∑ y : Bits (M + M + M),
            (starRingEnd ℂ) (tensor (tensor (u i.1.1) (u i.1.2)) (u i.2) y)
              * tensor (tensor (u j.1.1) (u j.1.2)) (u j.2) y)
          = if i = j then 1 else 0)
      ∧ (∀ z : Bits (M + M + M) → ℂ,
        (∑ i : (Bits M × Bits M) × Bits M,
            ‖∑ y : Bits (M + M + M), (starRingEnd ℂ) (z y)
              * tensor (tensor (u i.1.1) (u i.1.2)) (u i.2) y‖ ^ 2)
          = ∑ y : Bits (M + M + M), ‖z y‖ ^ 2) := by
  sorry

end ShiShallow
