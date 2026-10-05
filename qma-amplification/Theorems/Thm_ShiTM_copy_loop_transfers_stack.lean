-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.copy_loop_transfers_stack`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_copy_loop_transfers_stack`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiTM

theorem copy_loop_transfers_stack {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) {ka kb : K} (hab : ka ≠ kb) {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool} {hpush : σ → Γ kb} {e : Γ ka → Γ kb}
    (hM : M lc = Turing.TM2.Stmt.pop ka fpop
            (Turing.TM2.Stmt.branch gtest
              (Turing.TM2.Stmt.push kb hpush (Turing.TM2.Stmt.goto (fun _ => lc)))
              (Turing.TM2.Stmt.goto (fun _ => lnext))))
    (hcont : ∀ (w : σ) (y : Γ ka), gtest (fpop w (some y)) = true)
    (hstop : ∀ w : σ, gtest (fpop w none) = false)
    (hval : ∀ (w : σ) (y : Γ ka), hpush (fpop w (some y)) = e y)
    (s : List (Γ ka)) (v : σ) (S : ∀ k, List (Γ k)) (hS : S ka = s) :
    (fun c : Option (Turing.TM2.Cfg Γ Λ σ) => c.bind (Turing.TM2.step M))^[s.length + 1]
        (some { l := some lc, var := v, stk := S })
      = some { l := some lnext,
               var := fpop (s.foldl (fun w y => fpop w (some y)) v) none,
               stk := Function.update (Function.update S ka []) kb
                        ((s.map e).reverse ++ S kb) }
    ∧ Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step M)
        { l := some lc, var := v, stk := S }
        (some { l := some lnext,
                var := fpop (s.foldl (fun w y => fpop w (some y)) v) none,
                stk := Function.update (Function.update S ka []) kb
                         ((s.map e).reverse ++ S kb) })
        (s.length + 1)) := by
  sorry

end ShiTM
