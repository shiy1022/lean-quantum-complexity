-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.majority_weight_eq_conj_majority_quadratic_form`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_majority_weight_eq_conj_majority_quadratic_form`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix
import Theorems.Thm_ShiShallow_projOut_majority_inclusion_exclusion
import Theorems.Thm_ShiShallow_conj_majority_inclusion_exclusion_of_unitary

set_option autoImplicit false

namespace ShiShallow

theorem majority_weight_eq_conj_majority_quadratic_form {N : ℕ} (V : Op N) (hV : star V * V = (1 : Op N))
    (w1 w2 w3 : Fin N) (Φ : Bits N → ℂ) :
    (∑ y : Bits N,
        if 2 ≤ (if y w1 = true then (1 : ℕ) else 0) + (if y w2 = true then (1 : ℕ) else 0)
              + (if y w3 = true then (1 : ℕ) else 0)
          then ‖Matrix.mulVec V Φ y‖ ^ 2 else 0)
      = (∑ y : Bits N, (starRingEnd ℂ) (Φ y) * Matrix.mulVec
            ((star V * projOut w1 * V) * (star V * projOut w2 * V)
              + (star V * projOut w2 * V) * (star V * projOut w3 * V)
              + (star V * projOut w3 * V) * (star V * projOut w1 * V)
              - 2 * ((star V * projOut w1 * V) * (star V * projOut w2 * V)
                  * (star V * projOut w3 * V))) Φ y).re := by
  sorry

end ShiShallow
