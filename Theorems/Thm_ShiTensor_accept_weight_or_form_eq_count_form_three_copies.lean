-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTensor.accept_weight_or_form_eq_count_form_three_copies`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTensor_accept_weight_or_form_eq_count_form_three_copies`. The real proof is on prove2.me.
import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

namespace ShiTensor

open ShiShallow ShiTensor

theorem accept_weight_or_form_eq_count_form_three_copies {M : ℕ} (out : Fin M) (A : QState M) :
    (∑ v : Bits (M + M + M),
        if ((v (Fin.castAdd M (Fin.castAdd M out)) && v (Fin.castAdd M (Fin.natAdd M out)))
            || ((v (Fin.castAdd M (Fin.natAdd M out)) && v (Fin.natAdd (M + M) out))
              || (v (Fin.castAdd M (Fin.castAdd M out)) && v (Fin.natAdd (M + M) out))))
        then ‖tensor (tensor A A) A v‖ ^ 2 else 0)
      = ∑ y : Bits (M + (M + M)),
          (if 2 ≤ (if leftBits y out then (1 : ℕ) else 0)
                + (if leftBits (rightBits y) out then (1 : ℕ) else 0)
                + (if rightBits (rightBits y) out then (1 : ℕ) else 0)
            then ‖tensor A (tensor A A) y‖ ^ 2 else 0) := by
  sorry

end ShiTensor
