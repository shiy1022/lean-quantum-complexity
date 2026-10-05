-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMA.acceptWith_eq_quadratic_form`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMA_acceptWith_eq_quadratic_form`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMA
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiClassQMA

open ShiShallow

theorem acceptWith_eq_quadratic_form {n : ℕ} (F : QMAFamily) (x : Bits n)
    (ψ : QState (F.wit n)) :
    F.acceptWith x ψ
      = (∑ y : Bits (n + (F.wit n + (F.anc n + 1))),
          (starRingEnd ℂ) (witnessInputState F x ψ y)
            * Matrix.mulVec
                (star (circMatrix (F.circ n)) * projOut (F.out n) * circMatrix (F.circ n))
                (witnessInputState F x ψ) y).re := by
  sorry

end ShiClassQMA
