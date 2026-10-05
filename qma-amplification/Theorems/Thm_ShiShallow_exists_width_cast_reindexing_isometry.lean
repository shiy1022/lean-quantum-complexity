-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiShallow.exists_width_cast_reindexing_isometry`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiShallow_exists_width_cast_reindexing_isometry`. The real proof is on prove2.me.
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

namespace ShiShallow

open ShiShallow

theorem exists_width_cast_reindexing_isometry {K M : ℕ} (h : K = M) :
    ∃ R : Matrix (Bits K) (Bits M) ℂ,
      Matrix.conjTranspose R * R = (1 : Op M) ∧
      (∀ Ψ : QState M,
          Matrix.mulVec R Ψ
            = fun z : Bits K => Ψ (fun i : Fin M => z (Fin.cast h.symm i))) ∧
      (∀ Ψ : QState M,
          (∑ z : Bits K, ‖Matrix.mulVec R Ψ z‖ ^ 2)
            = ∑ y : Bits M, ‖Ψ y‖ ^ 2) := by
  sorry

end ShiShallow
