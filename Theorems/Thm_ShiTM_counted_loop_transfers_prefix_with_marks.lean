-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.counted_loop_transfers_prefix_with_marks`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_counted_loop_transfers_prefix_with_marks`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiTM

open Turing Turing.TM2 Turing.TM2.Stmt

theorem counted_loop_transfers_prefix_with_marks {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Turing.TM2.Stmt Gam Lam sig) {ka kb kc : K}
    (hab : ka ≠ kb) (hac : ka ≠ kc) (hbc : kb ≠ kc) {lc lnext : Lam}
    {fpop : sig → Option (Gam ka) → sig} {gtest : sig → Bool}
    {hpush : sig → Gam kb} {hmark : sig → Gam kc}
    {e : Gam ka → Gam kb} {mk : Gam ka → Gam kc}
    (hM : M lc = Turing.TM2.Stmt.pop ka fpop
            (Turing.TM2.Stmt.branch gtest
              (Turing.TM2.Stmt.push kb hpush
                (Turing.TM2.Stmt.push kc hmark (Turing.TM2.Stmt.goto (fun _ => lc))))
              (Turing.TM2.Stmt.goto (fun _ => lnext))))
    (hval : forall (w : sig) (y : Gam ka), hpush (fpop w (some y)) = e y)
    (hmkv : forall (w : sig) (y : Gam ka), hmark (fpop w (some y)) = mk y)
    (p : List (Gam ka))
    (hcont : forall (w : sig) (y : Gam ka), y ∈ p → gtest (fpop w (some y)) = true)
    (c : Gam ka) (hstop : forall w : sig, gtest (fpop w (some c)) = false) (t : List (Gam ka))
    (v : sig) (S : forall k, List (Gam k)) (hS : S ka = p ++ c :: t) :
    (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) => cf.bind (Turing.TM2.step M))^[p.length + 1]
        (some { l := some lc, var := v, stk := S })
      = some { l := some lnext,
               var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
               stk := Function.update
                        (Function.update (Function.update S ka t) kb
                          ((List.map e p).reverse ++ S kb))
                        kc ((List.map mk p).reverse ++ S kc) }
    ∧ Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step M)
        { l := some lc, var := v, stk := S }
        (some { l := some lnext,
                var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
                stk := Function.update
                         (Function.update (Function.update S ka t) kb
                           ((List.map e p).reverse ++ S kb))
                         kc ((List.map mk p).reverse ++ S kc) })
        (p.length + 1))
    ∧ ((List.map mk p).reverse ++ S kc).length = p.length + (S kc).length
    ∧ (forall m : Gam kc, (forall y : Gam ka, mk y = m) →
          (List.map mk p).reverse ++ S kc = List.replicate p.length m ++ S kc) := by
  sorry

end ShiTM
