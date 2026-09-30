-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.cnotState_eq_cnotMatrix_mulVec`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_cnotState_eq_cnotMatrix_mulVec`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

open Matrix

theorem cnotState_eq_cnotMatrix_mulVec {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n) :
    cnotState i j hij ψ = cnotMatrix i j *ᵥ ψ := by
  sorry

end ShiShallow
