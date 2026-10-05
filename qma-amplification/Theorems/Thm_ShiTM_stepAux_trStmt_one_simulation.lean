-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.stepAux_trStmt_one_simulation`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_stepAux_trStmt_one_simulation`. The real proof is on prove2.me.
import Definitions.Def_ShiTM2_Composite

set_option autoImplicit false

namespace ShiTM

open Turing.TM2 ShiTM2

theorem stepAux_trStmt_one_simulation (tm₁ tm₂ : Turing.FinTM2) [DecidableEq tm₁.K]
    [DecidableEq (CompK tm₁ tm₂)] (T : ∀ k, List (CompΓ tm₁ tm₂ k)) :
    (∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i)),
        stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)
          = liftCfg₁ tm₁ tm₂ T w.2.1 w.2.2 (stepAux q w.1 S))
  ∧ (∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i)),
        (stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)).var
            = ((stepAux q w.1 S).var, w.2.1, w.2.2)
      ∧ (stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)).stk
            = liftStk₁ tm₁ tm₂ T (stepAux q w.1 S).stk)
  ∧ (∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i))
        (l : tm₁.Λ), (stepAux q w.1 S).l = Option.some l →
        (stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)).l
          = Option.some (injΛ₁ tm₁ tm₂ l))
  ∧ (∀ (q : Stmt tm₁.Γ tm₁.Λ tm₁.σ) (w : Compσ tm₁ tm₂) (S : ∀ i, List (tm₁.Γ i)),
        (stepAux q w.1 S).l = Option.none →
        (stepAux (trStmt₁ tm₁ tm₂ q) w (liftStk₁ tm₁ tm₂ T S)).l
          = Option.some (lcopyA tm₁ tm₂)) := by
  sorry

end ShiTM
