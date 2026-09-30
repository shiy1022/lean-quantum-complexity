-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTensor.tensor_split_append_inverse`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTensor_tensor_split_append_inverse`. The real proof is on prove2.me.
import Definitions.Def_ShiTensor_Core

set_option autoImplicit false

open ShiShallow

namespace ShiTensor

theorem tensor_split_append_inverse {m p : ℕ} :
    (∀ (a : Bits m) (b : Bits p), leftBits (Fin.append a b) = a) ∧
    (∀ (a : Bits m) (b : Bits p), rightBits (Fin.append a b) = b) ∧
    (∀ (y : Bits (m + p)), Fin.append (leftBits y) (rightBits y) = y) := by
  sorry

end ShiTensor
