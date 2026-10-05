-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.exists_majority_readout_at_wires_layerOk_depth`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_exists_majority_readout_at_wires_layerOk_depth`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Core
import Theorems.Thm_ShiShallow_exists_toffoli_at_wires_layerOk_depth
import Theorems.Thm_ShiShallow_runLayered_append_action_readout

set_option autoImplicit false

namespace ShiShallow

theorem exists_majority_readout_at_wires_layerOk_depth {N : ℕ} (w1 w2 w3 s : Fin N)
    (h12 : w1 ≠ w2) (h13 : w1 ≠ w3) (h23 : w2 ≠ w3)
    (h1s : w1 ≠ s) (h2s : w2 ≠ s) (h3s : w3 ≠ s) :
    ∃ c : Layered N,
      (∀ ψ : QState N, runLayered c ψ
          = fun x => ψ (Function.update x s
              (xor (x s) (xor (xor (x w1 && x w2) (x w2 && x w3)) (x w1 && x w3)))))
      ∧ (∀ l ∈ c, LayerOk l)
      ∧ depth c = 111 := by
  sorry

end ShiShallow
