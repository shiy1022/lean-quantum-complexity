-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiEmbed.layerOk_closure_append_embedCirc`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiEmbed_layerOk_closure_append_embedCirc`. The real proof is on prove2.me.
import Definitions.Def_ShiEmbed_Core

set_option autoImplicit false

namespace ShiEmbed

open ShiShallow

theorem layerOk_closure_append_embedCirc {m n : ℕ}
    (e : Fin m → Fin n) (he : Function.Injective e) :
    (∀ (c : Layered m), (∀ l ∈ c, LayerOk l) →
        ∀ l ∈ ShiEmbed.embedCirc e he c, LayerOk l)
      ∧ (∀ (c1 c2 : Layered n), (∀ l ∈ c1, LayerOk l) → (∀ l ∈ c2, LayerOk l) →
        ∀ l ∈ c1 ++ c2, LayerOk l) := by
  sorry

end ShiEmbed
