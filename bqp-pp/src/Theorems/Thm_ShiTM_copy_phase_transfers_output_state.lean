-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.copy_phase_transfers_output_state`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_copy_phase_transfers_output_state`. The real proof is on prove2.me.
import Definitions.Def_ShiTM2_Composite
import Theorems.Thm_ShiTM_copy_loop_transfers_stack

set_option autoImplicit false

namespace ShiTM

open ShiTM2

theorem copy_phase_transfers_output_state (tm₁ tm₂ : Turing.FinTM2) [DecidableEq (ShiTM2.CompK tm₁ tm₂)]
    (tr : tm₁.Γ tm₁.k₁ → tm₂.Γ tm₂.k₀) (dflt : tm₂.Γ tm₂.k₀)
    (v : ShiTM2.Compσ tm₁ tm₂) (S : ∀ k, List (ShiTM2.CompΓ tm₁ tm₂ k))
    (hscr : S (ShiTM2.kScr tm₁ tm₂) = [])
    (hin : S (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀) = []) :
    ∃ (v' : ShiTM2.Compσ tm₁ tm₂) (S' : ∀ k, List (ShiTM2.CompΓ tm₁ tm₂ k)),
      (fun c : Option (ShiTM2.CompCfg tm₁ tm₂) =>
            c.bind (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt)))^[
          2 * (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length + 2]
            (some { l := some (ShiTM2.lcopyA tm₁ tm₂), var := v, stk := S })
          = some { l := some (ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main), var := v', stk := S' }
      ∧ Nonempty (StateTransition.EvalsToInTime
            (Turing.TM2.step (ShiTM2.compM tm₁ tm₂ tr dflt))
            { l := some (ShiTM2.lcopyA tm₁ tm₂), var := v, stk := S }
            (some { l := some (ShiTM2.injΛ₂ tm₁ tm₂ tm₂.main), var := v', stk := S' })
            (2 * (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).length + 2))
      ∧ S' (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀)
          = (S (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁)).map
              (tr : ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) →
                    ShiTM2.CompΓ tm₁ tm₂ (ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀))
      ∧ S' (ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁) = []
      ∧ S' (ShiTM2.kScr tm₁ tm₂) = []
      ∧ (∀ k, k ≠ ShiTM2.injK₁ tm₁ tm₂ tm₁.k₁ → k ≠ ShiTM2.injK₂ tm₁ tm₂ tm₂.k₀ →
          k ≠ ShiTM2.kScr tm₁ tm₂ → S' k = S k)
      ∧ v' = (v.1, v.2.1, Option.none) := by
  sorry

end ShiTM
