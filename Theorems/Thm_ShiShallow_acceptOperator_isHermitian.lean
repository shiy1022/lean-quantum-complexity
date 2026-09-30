-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.acceptOperator_isHermitian`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_acceptOperator_isHermitian`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem acceptOperator_isHermitian {n : ℕ} (A : Op n) (out : Fin n) :
    (star A * projOut out * A).IsHermitian := by
  sorry

end ShiShallow
