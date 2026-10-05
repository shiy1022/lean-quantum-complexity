-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.circMatrix_unitary`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_circMatrix_unitary`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem circMatrix_unitary {n : ℕ} (c : Layered n) :
    star (circMatrix c) * circMatrix c = (1 : Op n) := by
  sorry

end ShiShallow
