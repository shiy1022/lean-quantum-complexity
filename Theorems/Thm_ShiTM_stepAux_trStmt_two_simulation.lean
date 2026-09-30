-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.stepAux_trStmt_two_simulation`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_stepAux_trStmt_two_simulation`. The real proof is on prove2.me.
import Definitions.Def_ShiTM2_Composite

set_option autoImplicit false

namespace ShiTM

open Turing.TM2 ShiTM2

theorem stepAux_trStmt_two_simulation (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₂.K]
    [DecidableEq (CompK tm₁ tm₂)] (T : ∀ k, List (CompΓ tm₁ tm₂ k)) :
    (∀ (q : Stmt tm₂.Γ tm₂.Λ tm₂.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₂.Γ i)),
        stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)
          = liftCfg₂ tm₁ tm₂ T w.1 w.2.2 (stepAux q w.2.1 S))
  ∧ (∀ (q : Stmt tm₂.Γ tm₂.Λ tm₂.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₂.Γ i)),
        (stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)).var
            = (w.1, (stepAux q w.2.1 S).var, w.2.2)
      ∧ (stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)).stk
            = liftStk₂ tm₁ tm₂ T (stepAux q w.2.1 S).stk)
  ∧ (∀ (q : Stmt tm₂.Γ tm₂.Λ tm₂.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₂.Γ i)),
        (stepAux (trStmt₂ tm₁ tm₂ q) w (liftStk₂ tm₁ tm₂ T S)).l
          = ((stepAux q w.2.1 S).l).map (injΛ₂ tm₁ tm₂)) := by
  sorry

end ShiTM
