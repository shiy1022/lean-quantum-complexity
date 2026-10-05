-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.gateCount_le_depth_mul_width_of_layerOk_core`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_gateCount_le_depth_mul_width_of_layerOk_core`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

namespace ShiShallow

theorem gateCount_le_depth_mul_width_of_layerOk_core {n : ℕ} (c : Layered n) (hc : ∀ l ∈ c, LayerOk l) :
    (c.map List.length).sum ≤ depth c * n := by
  sorry

end ShiShallow
