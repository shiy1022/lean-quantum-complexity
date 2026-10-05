-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.runLayered_eq_circMatrix_mulVec`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_runLayered_eq_circMatrix_mulVec`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

open Matrix

theorem runLayered_eq_circMatrix_mulVec {n : ℕ}
    (hA : ∀ (U : Matrix Bool Bool ℂ) (i : Fin n) (ψ : QState n),
      apply1 U i ψ = apply1Matrix U i *ᵥ ψ)
    (hC : ∀ (i j : Fin n) (hij : i ≠ j) (ψ : QState n),
      cnotState i j hij ψ = cnotMatrix i j *ᵥ ψ)
    (c : Layered n) (ψ : QState n) :
    runLayered c ψ = circMatrix c *ᵥ ψ := by
  sorry

end ShiShallow
