-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.iterate_compM_one_simulation`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_iterate_compM_one_simulation`. The real proof is on prove2.me.
import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_stepAux_trStmt_one_simulation

set_option autoImplicit false

namespace ShiTM

open Turing.TM2 ShiTM2

theorem iterate_compM_one_simulation (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₂ : tm₂.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (n : ℕ) (l : tm₁.Λ) (v : tm₁.σ)
    (S : ∀ i, List (tm₁.Γ i))
    (hlive : ∀ j < n, ∃ (l' : tm₁.Λ) (v' : tm₁.σ) (S' : ∀ i, List (tm₁.Γ i)),
        (fun c : Option (Cfg tm₁.Γ tm₁.Λ tm₁.σ) => c.bind (step tm₁.m))^[j]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ))
          = Option.some (⟨Option.some l', v', S'⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ)) :
    (fun c : Option (CompCfg tm₁ tm₂) => c.bind (step (compM tm₁ tm₂ tr dflt)))^[n]
        (Option.some (liftCfg₁ tm₁ tm₂ T w₂ r ⟨Option.some l, v, S⟩))
      = ((fun c : Option (Cfg tm₁.Γ tm₁.Λ tm₁.σ) => c.bind (step tm₁.m))^[n]
          (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ))).map
            (liftCfg₁ tm₁ tm₂ T w₂ r)
  ∧ (∀ c : Cfg tm₁.Γ tm₁.Λ tm₁.σ,
        (fun c : Option (Cfg tm₁.Γ tm₁.Λ tm₁.σ) => c.bind (step tm₁.m))^[n]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₁.Γ tm₁.Λ tm₁.σ))
          = Option.some c →
        Nonempty (StateTransition.EvalsToInTime (step (compM tm₁ tm₂ tr dflt))
          (liftCfg₁ tm₁ tm₂ T w₂ r ⟨Option.some l, v, S⟩)
          (Option.some (liftCfg₁ tm₁ tm₂ T w₂ r c)) n)) := by
  sorry

end ShiTM
