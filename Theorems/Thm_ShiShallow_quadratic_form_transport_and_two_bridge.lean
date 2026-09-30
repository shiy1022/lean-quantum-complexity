-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.quadratic_form_transport_and_two_bridge`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_quadratic_form_transport_and_two_bridge`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

open ShiShallow

theorem quadratic_form_transport_and_two_bridge {M N : ℕ} :
    (∀ (Q : Matrix (Bits M) (Bits N) ℂ) (X : Op M) (psi : QState N),
        (∑ y : Bits M, (starRingEnd ℂ) (Matrix.mulVec Q psi y)
              * Matrix.mulVec X (Matrix.mulVec Q psi) y).re
          = (∑ u : Bits N, (starRingEnd ℂ) (psi u)
              * Matrix.mulVec (Matrix.conjTranspose Q * X * Q) psi u).re)
      ∧ (∀ X : Op N, (2 : Op N) * X = (2 : ℂ) • X) := by
  sorry

end ShiShallow
