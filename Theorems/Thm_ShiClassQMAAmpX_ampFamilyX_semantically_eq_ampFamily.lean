-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMAAmpX.ampFamilyX_semantically_eq_ampFamily`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_semantically_eq_ampFamily`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMAAmpX
import Theorems.Thm_ShiShallow_explicit_embedded_fanout_circuit
import Theorems.Thm_ShiShallow_explicit_toffoli_majority_readout_and_fanout_circuits

set_option autoImplicit false

open ShiShallow ShiClassQMA ShiClassQMAAmp ShiClassQMAAmpX

namespace ShiClassQMAAmpX

theorem ampFamilyX_semantically_eq_ampFamily (F : QMAFamily) (n : ℕ)
    (Φ : QState (n + ((ampFamily F).wit n + ((ampFamily F).anc n + 1)))) :
    runLayered ((ampFamilyX F).circ n) Φ = runLayered ((ampFamily F).circ n) Φ := by
  sorry

end ShiClassQMAAmpX
