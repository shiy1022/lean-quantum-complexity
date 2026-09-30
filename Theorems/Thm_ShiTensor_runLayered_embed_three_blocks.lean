-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTensor.runLayered_embed_three_blocks`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTensor_runLayered_embed_three_blocks`. The real proof is on prove2.me.
import Definitions.Def_ShiTensor_Core
import Definitions.Def_ShiEmbed_Core

set_option autoImplicit false

namespace ShiTensor

open ShiShallow

theorem runLayered_embed_three_blocks {m p q : ℕ} (c1 : Layered m) (c2 : Layered p) (c3 : Layered q)
    (ψ1 : QState m) (ψ2 : QState p) (ψ3 : QState q) :
    runLayered
        (ShiEmbed.embedCirc
            ((Fin.castAdd q : Fin (m + p) → Fin (m + p + q)) ∘
              (Fin.castAdd p : Fin m → Fin (m + p)))
            ((Fin.castAdd_injective (m + p) q).comp (Fin.castAdd_injective m p)) c1
          ++ ShiEmbed.embedCirc
            ((Fin.castAdd q : Fin (m + p) → Fin (m + p + q)) ∘
              (Fin.natAdd m : Fin p → Fin (m + p)))
            ((Fin.castAdd_injective (m + p) q).comp (Fin.natAdd_injective p m)) c2
          ++ ShiEmbed.embedCirc (Fin.natAdd (m + p) : Fin q → Fin (m + p + q))
            (Fin.natAdd_injective q (m + p)) c3)
        (tensor (tensor ψ1 ψ2) ψ3)
      = tensor (tensor (runLayered c1 ψ1) (runLayered c2 ψ2)) (runLayered c3 ψ3) := by
  sorry

end ShiTensor
