-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.apply1_eq_apply1Matrix_mulVec`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_apply1_eq_apply1Matrix_mulVec`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem apply1_eq_apply1Matrix_mulVec {n : ℕ} (U : Matrix Bool Bool ℂ) (i : Fin n)
    (ψ : QState n) :
    apply1 U i ψ = Matrix.mulVec (apply1Matrix U i) ψ := by
  sorry

end ShiShallow
