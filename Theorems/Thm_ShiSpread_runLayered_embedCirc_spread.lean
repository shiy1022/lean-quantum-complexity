-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiSpread.runLayered_embedCirc_spread`, statement verbatim, body `sorry` as the platform
-- stores targets, so solutions can cite it as a tracked reduction.
import Definitions.Def_ShiSpread_Core

namespace ShiSpread

open ShiEmbed ShiShallow in
theorem runLayered_embedCirc_spread {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (c : Layered m) (ψ : QState m) :
    runLayered (embedCirc e he c) (spread e ψ) = spread e (runLayered c ψ) := by sorry

end ShiSpread
