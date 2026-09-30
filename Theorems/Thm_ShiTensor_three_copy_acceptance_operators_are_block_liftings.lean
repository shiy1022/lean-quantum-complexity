-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTensor.three_copy_acceptance_operators_are_block_liftings`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTensor_three_copy_acceptance_operators_are_block_liftings`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix
import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiEmbed_Core
import Theorems.Thm_ShiTensor_runLayered_embed_three_blocks
import Theorems.Thm_ShiTensor_sum_split_factor
import Theorems.Thm_ShiTensor_tensor_split_append_inverse
import Theorems.Thm_ShiShallow_runLayered_eq_circMatrix_mulVec
import Theorems.Thm_ShiShallow_apply1_eq_apply1Matrix_mulVec
import Theorems.Thm_ShiShallow_cnotState_eq_cnotMatrix_mulVec
import Theorems.Thm_ShiShallow_circMatrix_unitary

set_option autoImplicit false

namespace ShiTensor

open ShiShallow ShiTensor

theorem three_copy_acceptance_operators_are_block_liftings {M : ℕ} (c : Layered M) (out : Fin M)
    (C3 : Layered (M + M + M))
    (hC3 : C3 =
      ShiEmbed.embedCirc
          ((Fin.castAdd M : Fin (M + M) → Fin (M + M + M)) ∘
            (Fin.castAdd M : Fin M → Fin (M + M)))
          ((Fin.castAdd_injective (M + M) M).comp (Fin.castAdd_injective M M)) c
        ++ ShiEmbed.embedCirc
          ((Fin.castAdd M : Fin (M + M) → Fin (M + M + M)) ∘
            (Fin.natAdd M : Fin M → Fin (M + M)))
          ((Fin.castAdd_injective (M + M) M).comp (Fin.natAdd_injective M M)) c
        ++ ShiEmbed.embedCirc (Fin.natAdd (M + M) : Fin M → Fin (M + M + M))
          (Fin.natAdd_injective M (M + M)) c)
    (A : Op M) (hA : A = star (circMatrix c) * projOut out * circMatrix c)
    (L1 L2 L3 : Op (M + M + M))
    (hL1 : L1 = Matrix.of fun y z =>
      A (leftBits (leftBits y)) (leftBits (leftBits z))
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * (if rightBits y = rightBits z then 1 else 0))
    (hL2 : L2 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * A (rightBits (leftBits y)) (rightBits (leftBits z))
        * (if rightBits y = rightBits z then 1 else 0))
    (hL3 : L3 = Matrix.of fun y z =>
      (if leftBits (leftBits y) = leftBits (leftBits z) then 1 else 0)
        * (if rightBits (leftBits y) = rightBits (leftBits z) then 1 else 0)
        * A (rightBits y) (rightBits z)) :
    star (circMatrix C3) * projOut (Fin.castAdd M (Fin.castAdd M out)) * circMatrix C3 = L1
      ∧ star (circMatrix C3) * projOut (Fin.castAdd M (Fin.natAdd M out)) * circMatrix C3 = L2
      ∧ star (circMatrix C3) * projOut (Fin.natAdd (M + M) out) * circMatrix C3 = L3 := by
  sorry

end ShiTensor
