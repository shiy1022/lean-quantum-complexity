-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.exists_stepAux_stack_growth_bound`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_exists_stepAux_stack_growth_bound`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiTM

theorem exists_stepAux_stack_growth_bound {K : Type} [DecidableEq K] [Fintype K]
    {Γ : K → Type} {Λ σ : Type} [Fintype Λ] (M : Λ → Turing.TM2.Stmt Γ Λ σ) :
    ∃ c : ℕ, ∀ (l : Λ) (v : σ) (S : ∀ k, List (Γ k)),
      ∑ k, ((Turing.TM2.stepAux (M l) v S).stk k).length
        ≤ (∑ k, (S k).length) + c := by
  sorry

end ShiTM
