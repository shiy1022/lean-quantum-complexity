-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.comp_outputsInTime`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_comp_outputsInTime`. The real proof is on prove2.me.
import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_initList_haltList_laws
import Theorems.Thm_ShiTM_initList_haltList_comp
import Theorems.Thm_ShiTM_iterate_compM_one_simulation
import Theorems.Thm_ShiTM_iterate_compM_two_simulation
import Theorems.Thm_ShiTM_copy_phase_transfers_output_state

set_option autoImplicit false

namespace ShiTM

open ShiTM2

theorem comp_outputsInTime (tm₁ tm₂ : Turing.FinTM2) [inst : DecidableEq (ShiTM2.CompK tm₁ tm₂)]
    (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀) (dflt : tm₂.Γ tm₂.k₀)
    (s : List (tm₁.Γ tm₁.k₀)) (t : List (tm₁.Γ tm₁.k₁)) (u : List (tm₂.Γ tm₂.k₁))
    (m₁ m₂ : ℕ)
    (h₁ : Turing.TM2OutputsInTime tm₁ s (Option.some t) m₁)
    (h₂ : Turing.TM2OutputsInTime tm₂ (t.map tr) (Option.some u) m₂) :
    Nonempty (Turing.TM2OutputsInTime (ShiTM2.comp tm₁ tm₂ tr dflt) s (Option.some u)
      (m₁ + (2 * t.length + 2) + m₂)) := by
  sorry

end ShiTM
