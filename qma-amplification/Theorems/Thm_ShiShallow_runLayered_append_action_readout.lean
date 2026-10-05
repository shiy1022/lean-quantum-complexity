-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.runLayered_append_action_readout`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_runLayered_append_action_readout`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem runLayered_append_action_readout {N : ℕ} (cA cR : Layered N)
    (fA : QState N → QState N) (uR : Bits N → Bits N)
    (hA : ∀ ψ, runLayered cA ψ = fA ψ)
    (hR : ∀ ψ, runLayered cR ψ = fun x => ψ (uR x))
    (ψ : QState N) :
    runLayered (cA ++ cR) ψ = fun x => fA ψ (uR x) := by
  sorry

end ShiShallow
