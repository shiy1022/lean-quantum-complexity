-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMA.exists_witness_space_acceptance_operator`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMA_exists_witness_space_acceptance_operator`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMA
import Definitions.Def_ShiShallow_Matrix
import Theorems.Thm_ShiClassQMA_acceptWith_eq_quadratic_form
import Theorems.Thm_ShiShallow_acceptOperator_isHermitian

set_option autoImplicit false

namespace ShiClassQMA

open ShiShallow ShiClassQMA

theorem exists_witness_space_acceptance_operator {n : ℕ} (F : ShiClassQMA.QMAFamily) (x : Bits n) :
    ∃ A : Op (F.wit n),
      A.IsHermitian
      ∧ ∀ psi : QState (F.wit n),
          (∑ u : Bits (F.wit n), (starRingEnd ℂ) (psi u) * Matrix.mulVec A psi u).re
              = F.acceptWith x psi
            ∧ 0 ≤ F.acceptWith x psi := by
  sorry

end ShiClassQMA
