-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.initList_haltList_comp`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_initList_haltList_comp`. The real proof is on prove2.me.
import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_initList_haltList_laws

set_option autoImplicit false

namespace ShiTM

open ShiTM2

theorem initList_haltList_comp (tm₁ tm₂ : Turing.FinTM2) (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀)
    (s : List ((comp tm₁ tm₂ tr dflt).Γ (comp tm₁ tm₂ tr dflt).k₀))
    (t : List ((comp tm₁ tm₂ tr dflt).Γ (comp tm₁ tm₂ tr dflt).k₁)) :
    (Turing.initList (comp tm₁ tm₂ tr dflt) s).l
        = Option.some (injΛ₁ tm₁ tm₂ tm₁.main)
      ∧ (Turing.initList (comp tm₁ tm₂ tr dflt) s).var = compInitialState tm₁ tm₂
      ∧ (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk (injK₁ tm₁ tm₂ tm₁.k₀) = s
      ∧ (∀ k : CompK tm₁ tm₂, k ≠ injK₁ tm₁ tm₂ tm₁.k₀ →
          (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk k = [])
      ∧ (Turing.haltList (comp tm₁ tm₂ tr dflt) t).l = Option.none
      ∧ (Turing.haltList (comp tm₁ tm₂ tr dflt) t).var = compInitialState tm₁ tm₂
      ∧ (Turing.haltList (comp tm₁ tm₂ tr dflt) t).stk (injK₂ tm₁ tm₂ tm₂.k₁) = t
      ∧ (∀ k : CompK tm₁ tm₂, k ≠ injK₂ tm₁ tm₂ tm₂.k₁ →
          (Turing.haltList (comp tm₁ tm₂ tr dflt) t).stk k = [])
      ∧ (∀ i : tm₁.K, (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk (injK₁ tm₁ tm₂ i)
          = (Turing.initList tm₁ s).stk i)
      ∧ (∀ i : tm₂.K,
          (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk (injK₂ tm₁ tm₂ i) = [])
      ∧ (Turing.initList (comp tm₁ tm₂ tr dflt) s).stk (kScr tm₁ tm₂) = [] := by
  sorry

end ShiTM
