-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.projOut_majority_inclusion_exclusion`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_projOut_majority_inclusion_exclusion`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem projOut_majority_inclusion_exclusion {n : ℕ} (w1 w2 w3 : Fin n) :
    (Matrix.of fun y z => if y = z ∧ 2 ≤ (if y w1 = true then (1:ℕ) else 0)
            + (if y w2 = true then (1:ℕ) else 0) + (if y w3 = true then (1:ℕ) else 0)
          then (1:ℂ) else 0)
      = projOut w1 * projOut w2 + projOut w2 * projOut w3 + projOut w3 * projOut w1
          - 2 * (projOut w1 * projOut w2 * projOut w3) := by
  sorry

end ShiShallow
