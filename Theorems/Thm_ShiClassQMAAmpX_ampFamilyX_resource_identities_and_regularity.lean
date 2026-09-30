-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMAAmpX.ampFamilyX_resource_identities_and_regularity`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMAAmpX_ampFamilyX_resource_identities_and_regularity`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMAAmpX
import Theorems.Thm_ShiClassQMAAmp_ampFamily_resource_identities_and_depth
import Theorems.Thm_ShiClassQMA_polyBounded_of_affine_depth_size_bounds
import Theorems.Thm_ShiEmbed_layerOk_closure_append_embedCirc
import Theorems.Thm_ShiShallow_explicit_embedded_fanout_circuit
import Theorems.Thm_ShiShallow_explicit_toffoli_majority_readout_and_fanout_circuits

set_option autoImplicit false

open ShiShallow ShiClassQMA ShiClassQMAAmp ShiClassQMAAmpX

namespace ShiClassQMAAmpX

theorem ampFamilyX_resource_identities_and_regularity :
    (∀ (F : QMAFamily) (n : ℕ), (ampFamilyX F).wit n = 3 * F.wit n)
    ∧ (∀ (F : QMAFamily) (n : ℕ),
        (ampFamilyX F).anc n = 2 * n + 3 * F.anc n + 3)
    ∧ (∀ (F : QMAFamily) (n : ℕ),
        ((ampFamilyX F).out n).val = 3 * n + 3 * F.wit n + 3 * F.anc n + 3)
    ∧ (∀ (F : QMAFamily) (n : ℕ),
        depth ((ampFamilyX F).circ n) = 3 * depth (F.circ n) + 113)
    ∧ (∀ F : QMAFamily,
        ShiBQP.WellFormed F.toFamily → ShiBQP.WellFormed (ampFamilyX F).toFamily)
    ∧ (∀ F : QMAFamily,
        ShiBQP.PolyBounded F.toFamily → ShiBQP.PolyBounded (ampFamilyX F).toFamily)
    ∧ (∃ F : QMAFamily,
        (ampFamilyX F).wit 0 = 3
        ∧ (ampFamilyX F).anc 0 = 3
        ∧ ((ampFamilyX F).out 0).val = 6
        ∧ depth ((ampFamilyX F).circ 0) = 113) := by
  sorry

end ShiClassQMAAmpX
