-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.eigenvalues_nonneg_of_quadratic_form_nonneg`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_eigenvalues_nonneg_of_quadratic_form_nonneg`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem eigenvalues_nonneg_of_quadratic_form_nonneg {w : ℕ}
    (M : Matrix (Bits w) (Bits w) ℂ) (hM : M.IsHermitian)
    (hb : ∀ v : Bits w → ℂ,
      0 ≤ (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec M v y).re)
    (i : Bits w) :
    0 ≤ hM.eigenvalues i := by
  sorry

end ShiShallow
