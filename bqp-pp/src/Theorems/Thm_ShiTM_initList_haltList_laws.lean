-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.initList_haltList_laws`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_initList_haltList_laws`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiTM

theorem initList_haltList_laws (tm : Turing.FinTM2)
    (s : List (tm.Γ tm.k₀)) (t : List (tm.Γ tm.k₁)) :
    (Turing.initList tm s).l = Option.some tm.main
      ∧ (Turing.initList tm s).var = tm.initialState
      ∧ (Turing.initList tm s).stk tm.k₀ = s
      ∧ (∀ k : tm.K, k ≠ tm.k₀ → (Turing.initList tm s).stk k = [])
      ∧ (Turing.haltList tm t).l = Option.none
      ∧ (Turing.haltList tm t).var = tm.initialState
      ∧ (Turing.haltList tm t).stk tm.k₁ = t
      ∧ (∀ k : tm.K, k ≠ tm.k₁ → (Turing.haltList tm t).stk k = []) := by
  sorry

end ShiTM
