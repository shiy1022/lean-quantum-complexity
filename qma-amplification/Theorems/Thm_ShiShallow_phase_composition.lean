-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.phase_composition`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_phase_composition`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem phase_composition {n : ℕ} (f g : QState n → QState n) (a b : Bits n → ℂ)
    (hf : ∀ (φ : QState n) (x : Bits n), f φ x = a x * φ x)
    (hg : ∀ (φ : QState n) (x : Bits n), g φ x = b x * φ x)
    (ψ : QState n) :
    ∀ x : Bits n, g (f ψ) x = (b x * a x) * ψ x := by
  sorry

end ShiShallow
