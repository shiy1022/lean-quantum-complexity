-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `PvsNP.polyTimeComputable_comp`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_PvsNP_polyTimeComputable_comp`. The real proof is on prove2.me.


import Definitions.Def_PvsNPFrontier

namespace PvsNP
theorem polyTimeComputable_comp (f g : Str → Str)
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (g ∘ f) := by sorry
end PvsNP
