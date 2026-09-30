-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiSpread.embedInstr_apply_spread`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiSpread_embedInstr_apply_spread`. The real proof is on prove2.me.
import Definitions.Def_ShiSpread_Core

namespace ShiSpread

open ShiEmbed ShiShallow in
theorem embedInstr_apply_spread {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e)
    (g : Instr m) (ψ : QState m) :
    Instr.apply (embedInstr e he g) (spread e ψ) = spread e (Instr.apply g ψ) := by sorry

end ShiSpread
