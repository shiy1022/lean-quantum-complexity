-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiEmbed.embedCirc_depth_append_comp`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiEmbed_embedCirc_depth_append_comp`. The real proof is on prove2.me.
import Definitions.Def_ShiEmbed_Core

set_option autoImplicit false

namespace ShiEmbed

open ShiShallow

theorem embedCirc_depth_append_comp {m n p : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (f : Fin n → Fin p) (hf : Function.Injective f) :
    (∀ c : Layered m, ShiShallow.depth (ShiEmbed.embedCirc e he c) = ShiShallow.depth c)
      ∧ (∀ c₁ c₂ : Layered m, ShiEmbed.embedCirc e he (c₁ ++ c₂)
            = ShiEmbed.embedCirc e he c₁ ++ ShiEmbed.embedCirc e he c₂)
      ∧ (∀ c : Layered m, ShiEmbed.embedCirc (f ∘ e) (hf.comp he) c
            = ShiEmbed.embedCirc f hf (ShiEmbed.embedCirc e he c)) := by
  sorry

end ShiEmbed
