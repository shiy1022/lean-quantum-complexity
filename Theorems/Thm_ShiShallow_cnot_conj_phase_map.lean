-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.cnot_conj_phase_map`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_cnot_conj_phase_map`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem cnot_conj_phase_map {n : ℕ} (i j : Fin n) (hij : i ≠ j) (ψ : QState n)
    (F : QState n → QState n) (a : Bits n → ℂ)
    (hF : ∀ (φ : QState n) (y : Bits n), F φ y = a y * φ y) :
    cnotState i j hij (F (cnotState i j hij ψ))
      = fun x => a (Function.update x j (xor (x j) (x i))) * ψ x := by
  sorry

end ShiShallow
