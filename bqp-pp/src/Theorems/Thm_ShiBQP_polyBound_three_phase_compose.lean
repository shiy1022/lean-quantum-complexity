-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiBQP.polyBound_three_phase_compose`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiBQP_polyBound_three_phase_compose`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiBQP

theorem polyBound_three_phase_compose (p₁ p₂ : Polynomial ℕ) (c d : ℕ) :
    ∃ q : Polynomial ℕ, ∀ n m : ℕ, m ≤ n + c * Polynomial.eval n p₁ →
      Polynomial.eval n p₁ + (2 * m + d) + Polynomial.eval m p₂ ≤ Polynomial.eval n q := by
  sorry

end ShiBQP
