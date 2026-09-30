-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.eigenvalues_le_of_quadratic_form_le`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_eigenvalues_le_of_quadratic_form_le`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem eigenvalues_le_of_quadratic_form_le {w : ℕ}
    (M : Matrix (Bits w) (Bits w) ℂ) (hM : M.IsHermitian) (s : ℝ)
    (hb : ∀ v : Bits w → ℂ,
      (∑ y : Bits w, (starRingEnd ℂ) (v y) * Matrix.mulVec M v y).re
        ≤ s * ∑ y : Bits w, ‖v y‖ ^ 2)
    (i : Bits w) :
    hM.eigenvalues i ≤ s := by
  sorry

end ShiShallow
