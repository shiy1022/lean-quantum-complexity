-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.iterate_compM_two_simulation`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_iterate_compM_two_simulation`. The real proof is on prove2.me.
import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_stepAux_trStmt_two_simulation

set_option autoImplicit false

namespace ShiTM

open Turing.TM2 ShiTM2

theorem iterate_compM_two_simulation (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀)
    (dflt : tm₂.Γ tm₂.k₀) (T : ∀ k, List (CompΓ tm₁ tm₂ k)) (w₁ : tm₁.σ)
    (r : Option (tm₂.Γ tm₂.k₀)) (n : ℕ) (l : tm₂.Λ) (v : tm₂.σ)
    (S : ∀ i, List (tm₂.Γ i))
    (hlive : ∀ j < n, ∃ (l' : tm₂.Λ) (v' : tm₂.σ) (S' : ∀ i, List (tm₂.Γ i)),
        (fun c : Option (Cfg tm₂.Γ tm₂.Λ tm₂.σ) => c.bind (step tm₂.m))^[j]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ))
          = Option.some (⟨Option.some l', v', S'⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ)) :
    (fun c : Option (CompCfg tm₁ tm₂) => c.bind (step (compM tm₁ tm₂ tr dflt)))^[n]
        (Option.some (liftCfg₂ tm₁ tm₂ T w₁ r ⟨Option.some l, v, S⟩))
      = ((fun c : Option (Cfg tm₂.Γ tm₂.Λ tm₂.σ) => c.bind (step tm₂.m))^[n]
          (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ))).map
            (liftCfg₂ tm₁ tm₂ T w₁ r)
  ∧ (∀ c : Cfg tm₂.Γ tm₂.Λ tm₂.σ,
        (fun c : Option (Cfg tm₂.Γ tm₂.Λ tm₂.σ) => c.bind (step tm₂.m))^[n]
            (Option.some (⟨Option.some l, v, S⟩ : Cfg tm₂.Γ tm₂.Λ tm₂.σ))
          = Option.some c →
        Nonempty (StateTransition.EvalsToInTime (step (compM tm₁ tm₂ tr dflt))
          (liftCfg₂ tm₁ tm₂ T w₁ r ⟨Option.some l, v, S⟩)
          (Option.some (liftCfg₂ tm₁ tm₂ T w₁ r c)) n)) := by
  sorry

end ShiTM
