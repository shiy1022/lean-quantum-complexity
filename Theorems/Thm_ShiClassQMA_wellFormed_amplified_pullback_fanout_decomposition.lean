-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMA.wellFormed_amplified_pullback_fanout_decomposition`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMA_wellFormed_amplified_pullback_fanout_decomposition`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMA
import Definitions.Def_ShiEmbed_Core
import Theorems.Thm_ShiShallow_exists_fanout_embedded_pullback
import Theorems.Thm_ShiEmbed_layerOk_closure_append_embedCirc

set_option autoImplicit false

namespace ShiClassQMA

open ShiShallow ShiClassQMA

theorem wellFormed_amplified_pullback_fanout_decomposition (T : QMAFamily → QMAFamily)
    (hcirc : ∀ (F : QMAFamily) (n : ℕ),
      ∃ (g2 g3 : Fin (n + n) → Fin (n + ((T F).wit n + ((T F).anc n + 1))))
        (e1 e2 e3 : Fin (n + (F.wit n + (F.anc n + 1)))
          → Fin (n + ((T F).wit n + ((T F).anc n + 1))))
        (rd fan2 fan3 : Layered (n + ((T F).wit n + ((T F).anc n + 1))))
        (hg2 : Function.Injective g2) (hg3 : Function.Injective g3)
        (he1 : Function.Injective e1) (he2 : Function.Injective e2)
        (he3 : Function.Injective e3),
        fan2 = Classical.choose (exists_fanout_embedded_pullback n
                 (n + ((T F).wit n + ((T F).anc n + 1))) g2 hg2)
        ∧ fan3 = Classical.choose (exists_fanout_embedded_pullback n
                 (n + ((T F).wit n + ((T F).anc n + 1))) g3 hg3)
        ∧ (T F).circ n
            = fan2 ++ fan3
              ++ ShiEmbed.embedCirc e1 he1 (F.circ n)
              ++ ShiEmbed.embedCirc e2 he2 (F.circ n)
              ++ ShiEmbed.embedCirc e3 he3 (F.circ n) ++ rd
        ∧ (∀ l ∈ rd, LayerOk l)) :
    ∀ F : QMAFamily,
      ShiBQP.WellFormed F.toFamily → ShiBQP.WellFormed (T F).toFamily := by
  sorry

end ShiClassQMA
