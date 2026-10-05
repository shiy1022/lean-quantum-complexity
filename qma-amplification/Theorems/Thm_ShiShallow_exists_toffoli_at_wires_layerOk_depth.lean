-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.exists_toffoli_at_wires_layerOk_depth`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_exists_toffoli_at_wires_layerOk_depth`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core
import Theorems.Thm_ShiShallow_apply1_tMat_eq_phase
import Theorems.Thm_ShiShallow_cnot_conj_phase_map
import Theorems.Thm_ShiShallow_phase_composition
import Theorems.Thm_ShiShallow_ccz_phase_exponent_eq
import Theorems.Thm_ShiShallow_inv_sqrt_two_mul_self

set_option autoImplicit false

namespace ShiShallow

theorem exists_toffoli_at_wires_layerOk_depth {N : ℕ} (p q r : Fin N) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∃ c : Layered N,
      (∀ ψ : QState N, runLayered c ψ
          = fun x => ψ (Function.update x r (xor (x r) (x p && x q))))
      ∧ (∀ l ∈ c, LayerOk l)
      ∧ depth c = 37 := by
  sorry

end ShiShallow
