-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMA.exists_witnessInputState_isometry`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMA_exists_witnessInputState_isometry`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMA
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiClassQMA

open ShiShallow ShiClassQMA

theorem exists_witnessInputState_isometry {n : ℕ} (F : QMAFamily) (x : Bits n) :
    ∃ W : Matrix (Bits (n + (F.wit n + (F.anc n + 1)))) (Bits (F.wit n)) ℂ,
      Matrix.conjTranspose W * W = (1 : Op (F.wit n)) ∧
      ∀ ψ : QState (F.wit n),
        Matrix.mulVec W ψ = witnessInputState F x ψ := by
  sorry

end ShiClassQMA
