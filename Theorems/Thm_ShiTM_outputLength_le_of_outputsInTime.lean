-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.outputLength_le_of_outputsInTime`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_outputLength_le_of_outputsInTime`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Option.Basic
import Theorems.Thm_ShiTM_initList_haltList_laws

set_option autoImplicit false

attribute [local instance] Turing.FinTM2.kFin

namespace ShiTM

theorem outputLength_le_of_outputsInTime {tm : Turing.FinTM2} (c : ℕ)
    (hc : ∀ (l : tm.Λ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
      ∑ k, ((Turing.TM2.stepAux (tm.m l) v S).stk k).length ≤ (∑ k, (S k).length) + c)
    (s : List (tm.Γ tm.k₀)) (t : List (tm.Γ tm.k₁)) (m : ℕ)
    (h : Turing.TM2OutputsInTime tm s (Option.some t) m) :
    t.length ≤ s.length + c * m := by
  sorry

end ShiTM
