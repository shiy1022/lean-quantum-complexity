-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.conj_majority_inclusion_exclusion_of_unitary`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_conj_majority_inclusion_exclusion_of_unitary`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

theorem conj_majority_inclusion_exclusion_of_unitary {n : ℕ} (A P Q R : Op n)
    (hA : star A * A = (1 : Op n)) :
    star A * (P * Q + Q * R + R * P - 2 * (P * Q * R)) * A
      = (star A * P * A) * (star A * Q * A)
        + (star A * Q * A) * (star A * R * A)
        + (star A * R * A) * (star A * P * A)
        - 2 * ((star A * P * A) * (star A * Q * A) * (star A * R * A)) := by
  sorry

end ShiShallow
