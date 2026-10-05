-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.polyTimeComputable_of_machine_polybound`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_polyTimeComputable_of_machine_polybound`. The real proof is on prove2.me.
import Definitions.Def_PvsNP

set_option autoImplicit false

namespace ShiTM

open Turing

theorem polyTimeComputable_of_machine_polybound (tm : Turing.FinTM2) (ea : tm.Γ tm.k₀ ≃ Bool) (eb : tm.Γ tm.k₁ ≃ Bool)
    (f : PvsNP.Str → PvsNP.Str) (p : Polynomial ℕ)
    (hrun : ∀ s : PvsNP.Str, Nonempty (Turing.TM2OutputsInTime tm
      (List.map ea.invFun s) (Option.some (List.map eb.invFun (f s)))
      (p.eval s.length))) :
    PvsNP.PolyTimeComputable f := by
  sorry

end ShiTM
