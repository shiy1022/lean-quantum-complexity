-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiClassQMA.polyBounded_of_affine_depth_size_bounds`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiClassQMA_polyBounded_of_affine_depth_size_bounds`. The real proof is on prove2.me.
import Definitions.Def_ShiClassQMA

set_option autoImplicit false

namespace ShiClassQMA

theorem polyBounded_of_affine_depth_size_bounds (T : ShiClassQMA.QMAFamily → ShiClassQMA.QMAFamily)
    (ad bd cd asz bsz csz : ℕ)
    (hdepth : ∀ (F : ShiClassQMA.QMAFamily) (n : ℕ),
      ShiShallow.depth ((T F).circ n)
        ≤ ad * ShiShallow.depth (F.circ n) + bd * n + cd)
    (hsize : ∀ (F : ShiClassQMA.QMAFamily) (n : ℕ),
      (T F).wit n + (T F).anc n
        ≤ asz * (F.wit n + F.anc n) + bsz * n + csz) :
    ∀ F : ShiClassQMA.QMAFamily,
      ShiBQP.PolyBounded F.toFamily → ShiBQP.PolyBounded (T F).toFamily := by
  sorry

end ShiClassQMA
