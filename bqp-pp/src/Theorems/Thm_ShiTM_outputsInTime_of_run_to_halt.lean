-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.outputsInTime_of_run_to_halt`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_outputsInTime_of_run_to_halt`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_initList_haltList_laws

set_option autoImplicit false

namespace ShiTM

open Turing

theorem outputsInTime_of_run_to_halt (tm : Turing.FinTM2) (inp : List (tm.Γ tm.k₀))
    (out : List (tm.Γ tm.k₁)) :
    (∀ (lfin : tm.Λ) (S : ∀ k, List (tm.Γ k)) (N : ℕ),
        tm.m lfin = Turing.TM2.Stmt.halt →
        (fun cf : Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) =>
              cf.bind (Turing.TM2.step tm.m))^[N]
            (Option.some (Turing.initList tm inp))
          = Option.some { l := Option.some lfin, var := tm.initialState, stk := S } →
        S tm.k₁ = out →
        (∀ k, k ≠ tm.k₁ → S k = []) →
        Nonempty (Turing.TM2OutputsInTime tm inp (Option.some out) (N + 1)))
      ∧ (∀ (lfin : tm.Λ) (c1 : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ)
          (T : ∀ k, List (tm.Γ k)) (N M : ℕ),
        tm.m lfin = Turing.TM2.Stmt.halt →
        (fun cf : Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) =>
              cf.bind (Turing.TM2.step tm.m))^[N]
            (Option.some (Turing.initList tm inp))
          = Option.some c1 →
        (fun cf : Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) =>
              cf.bind (Turing.TM2.step tm.m))^[M] (Option.some c1)
          = Option.some { l := Option.some lfin, var := tm.initialState, stk := T } →
        T tm.k₁ = out →
        (∀ k, k ≠ tm.k₁ → T k = []) →
        Nonempty (Turing.TM2OutputsInTime tm inp (Option.some out) (M + N + 1))) := by
  sorry

end ShiTM
