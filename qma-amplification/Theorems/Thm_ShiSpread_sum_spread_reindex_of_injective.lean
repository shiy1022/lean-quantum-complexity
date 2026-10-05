-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiSpread.sum_spread_reindex_of_injective`, statement verbatim, body `sorry`.
import Definitions.Def_ShiSpread_Core
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ShiSpread

open ShiShallow in
theorem sum_spread_reindex_of_injective {m n : ℕ} (e : Fin m → Fin n)
    (he : Function.Injective e) (χ : QState m) (H : Bits m → ℂ → ℝ)
    (hH : ∀ z : Bits m, H z 0 = 0) :
    ∑ y : Bits n, H (restrict e y) (spread e χ y) = ∑ z : Bits m, H z (χ z) := by sorry

end ShiSpread
