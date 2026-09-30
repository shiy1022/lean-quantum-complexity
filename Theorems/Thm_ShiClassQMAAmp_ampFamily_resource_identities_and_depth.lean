-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMAAmp.ampFamily_resource_identities_and_depth`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMAAmp_ampFamily_resource_identities_and_depth`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMAAmp
import Theorems.Thm_ShiClassQMA_wellFormed_amplified_pullback_fanout_decomposition
import Theorems.Thm_ShiClassQMA_polyBounded_of_affine_depth_size_bounds

set_option autoImplicit false

open ShiShallow ShiClassQMA

namespace ShiClassQMAAmp

theorem ampFamily_resource_identities_and_depth :
    (∀ (F : ShiClassQMA.QMAFamily) (n : ℕ),
        (ShiClassQMAAmp.ampFamily F).wit n = 3 * F.wit n)
    ∧ (∀ (F : ShiClassQMA.QMAFamily) (n : ℕ),
        (ShiClassQMAAmp.ampFamily F).anc n = 2 * n + 3 * F.anc n + 3)
    ∧ (∀ (F : ShiClassQMA.QMAFamily) (n : ℕ),
        ((ShiClassQMAAmp.ampFamily F).out n).val
          = 3 * n + 3 * F.wit n + 3 * F.anc n + 3)
    ∧ (∀ (F : ShiClassQMA.QMAFamily) (n : ℕ),
        ShiShallow.depth ((ShiClassQMAAmp.ampFamily F).circ n)
          = 3 * ShiShallow.depth (F.circ n) + 113)
    ∧ (∀ F : ShiClassQMA.QMAFamily,
        ShiBQP.WellFormed F.toFamily →
          ShiBQP.WellFormed (ShiClassQMAAmp.ampFamily F).toFamily)
    ∧ (∀ F : ShiClassQMA.QMAFamily,
        ShiBQP.PolyBounded F.toFamily →
          ShiBQP.PolyBounded (ShiClassQMAAmp.ampFamily F).toFamily)
    ∧ (∃ F : ShiClassQMA.QMAFamily,
        (∀ n : ℕ, F.wit n = 1)
        ∧ (∀ n : ℕ, F.anc n = 0)
        ∧ (∀ n : ℕ, ShiShallow.depth (F.circ n) = 0)
        ∧ (ShiClassQMAAmp.ampFamily F).wit 0 = 3
        ∧ (ShiClassQMAAmp.ampFamily F).anc 0 = 3
        ∧ ((ShiClassQMAAmp.ampFamily F).out 0).val = 6
        ∧ ShiShallow.depth ((ShiClassQMAAmp.ampFamily F).circ 0) = 113) := by
  sorry

end ShiClassQMAAmp
