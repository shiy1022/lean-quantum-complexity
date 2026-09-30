-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.exists_sum_form_eigenbasis`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_exists_sum_form_eigenbasis`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem exists_sum_form_eigenbasis {w : ℕ}
    (M : Matrix (Bits w) (Bits w) ℂ) (hM : M.IsHermitian) :
    ∃ u : Bits w → (Bits w → ℂ),
      (∀ i j, (∑ y : Bits w, (starRingEnd ℂ) (u i y) * u j y) = if i = j then 1 else 0)
      ∧ (∀ z : Bits w → ℂ,
          (∑ i : Bits w, ‖∑ y : Bits w, (starRingEnd ℂ) (z y) * u i y‖ ^ 2)
            = ∑ y : Bits w, ‖z y‖ ^ 2)
      ∧ (∀ i, Matrix.mulVec M (u i)
          = fun y => ((hM.eigenvalues i : ℝ) : ℂ) * u i y) := by
  sorry

end ShiShallow
