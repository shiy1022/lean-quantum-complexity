import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_copy_loop_transfers_stack

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMEmitReverseCompose

private theorem iterTwo {A : Type} (f : A → A) (q₁ q₂ : ℕ) (x y z : A)
    (h₁ : f^[q₁] x = y) (h₂ : f^[q₂] y = z) :
    f^[q₁ + q₂] x = z := by
  rw [show q₁ + q₂ = q₂ + q₁ by omega, Function.iterate_add_apply, h₁, h₂]

/-- Compose any natural-order chunk emitter with one accepted stack-transfer pass.  The
temporary stack is drained, and the accumulator receives the internally reversed chunk.
This is precisely the per-chunk half of AMPUNI's two-reversal ordering pipeline. -/
theorem emit_then_reverse_into_accumulator
    {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Stmt Gam Lam sig) {ktmp kacc : K} (hta : ktmp ≠ kacc)
    {lemit lrev lnext : Lam}
    {fpop : sig → Option (Gam ktmp) → sig} {gtest : sig → Bool}
    {hpush : sig → Gam kacc} {e : Gam ktmp → Gam kacc}
    (q : ℕ) (start : Cfg Gam Lam sig) (vmid : sig)
    (S T : ∀ k, List (Gam k)) (chunk : List (Gam ktmp))
    (hemit :
      (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[q] (some start) =
        some { l := some lrev, var := vmid, stk := T })
    (htmp : T ktmp = chunk)
    (hMrev : M lrev = Stmt.pop ktmp fpop
      (Stmt.branch gtest
        (Stmt.push kacc hpush (Stmt.goto (fun _ => lrev)))
        (Stmt.goto (fun _ => lnext))))
    (hcont : ∀ (w : sig) (y : Gam ktmp), gtest (fpop w (some y)) = true)
    (hstop : ∀ w : sig, gtest (fpop w none) = false)
    (hval : ∀ (w : sig) (y : Gam ktmp), hpush (fpop w (some y)) = e y) :
    ∃ (vout : sig) (U : ∀ k, List (Gam k)),
      (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[q + (chunk.length + 1)]
          (some start) = some { l := some lnext, var := vout, stk := U }
      ∧ U kacc = (chunk.map e).reverse ++ T kacc
      ∧ U ktmp = []
      ∧ (∀ k, k ≠ ktmp → k ≠ kacc → U k = T k)
      ∧ Nonempty (StateTransition.EvalsToInTime (step M)
          start (some { l := some lnext, var := vout, stk := U })
          (q + (chunk.length + 1))) := by
  let vout := fpop (chunk.foldl (fun w y => fpop w (some y)) vmid) none
  let U := Function.update (Function.update T ktmp []) kacc
    ((chunk.map e).reverse ++ T kacc)
  have hcopy :=
    ShiTM.copy_loop_transfers_stack M hta hMrev hcont hstop hval chunk vmid T htmp
  have hrev :
      (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[chunk.length + 1]
          (some { l := some lrev, var := vmid, stk := T }) =
        some { l := some lnext, var := vout, stk := U } := by
    simpa [vout, U] using hcopy.1
  have hout : U kacc = (chunk.map e).reverse ++ T kacc := by
    simp [U]
  have hempty : U ktmp = [] := by
    simp [U, hta]
  have hframe : ∀ k, k ≠ ktmp → k ≠ kacc → U k = T k := by
    intro k hk1 hk2
    simp [U, Function.update_of_ne hk1, Function.update_of_ne hk2]
  let run : Option (Cfg Gam Lam sig) → Option (Cfg Gam Lam sig) :=
    fun cf => cf.bind (step M)
  have hall : run^[q + (chunk.length + 1)] (some start) =
      some { l := some lnext, var := vout, stk := U } :=
    iterTwo run q (chunk.length + 1) (some start)
      (some { l := some lrev, var := vmid, stk := T })
      (some { l := some lnext, var := vout, stk := U })
      (by simpa [run] using hemit) (by simpa [run] using hrev)
  refine ⟨vout, U, by simpa [run] using hall, hout, hempty, hframe, ?_⟩
  refine ⟨⟨⟨q + (chunk.length + 1), ?_⟩, le_rfl⟩⟩
  change (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[q + (chunk.length + 1)]
      (some start) = some { l := some lnext, var := vout, stk := U }
  simpa [run] using hall

end ShiTMEmitReverseCompose
