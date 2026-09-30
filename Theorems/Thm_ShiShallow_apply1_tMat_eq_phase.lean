-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.apply1_tMat_eq_phase`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_apply1_tMat_eq_phase`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem apply1_tMat_eq_phase {n : ℕ} (i : Fin n) (ψ : QState n) :
    apply1 tMat i ψ = fun x => (if x i then Complex.exp (Complex.I * Real.pi / 4) else 1) * ψ x := by
  sorry

end ShiShallow
