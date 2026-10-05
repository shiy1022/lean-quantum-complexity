-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.encNat_parser_block`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_encNat_parser_block`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable
import Theorems.Thm_ShiTM_branch_loop_transfers_prefix_until_symbol
import Definitions.Def_ShiBQP_Core

set_option autoImplicit false

namespace ShiTM

open Turing Turing.TM2 Turing.TM2.Stmt

theorem encNat_parser_block {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Turing.TM2.Stmt Gam Lam sig) {ka kb : K} (hab : ka ≠ kb) {lc lnext : Lam}
    {fpop : sig → Option (Gam ka) → sig} {gtest : sig → Bool} {hpush : sig → Gam kb}
    {e : Gam ka → Gam kb} (b : Bool → Gam ka)
    (hM : M lc = Turing.TM2.Stmt.pop ka fpop
            (Turing.TM2.Stmt.branch gtest
              (Turing.TM2.Stmt.push kb hpush (Turing.TM2.Stmt.goto (fun _ => lc)))
              (Turing.TM2.Stmt.goto (fun _ => lnext))))
    (hval : forall (w : sig) (y : Gam ka), hpush (fpop w (some y)) = e y)
    (hone : forall w : sig, gtest (fpop w (some (b true))) = true)
    (hzero : forall w : sig, gtest (fpop w (some (b false))) = false)
    (k : ℕ) (rest : List (Gam ka)) (v : sig) (S : forall j, List (Gam j))
    (hS : S ka = (ShiBQP.encNat k).map b ++ rest) :
    (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) => cf.bind (Turing.TM2.step M))^[k + 1]
        (some { l := some lc, var := v, stk := S })
      = some { l := some lnext,
               var := fpop (List.foldl (fun w y => fpop w (some y)) v
                        (List.replicate k (b true))) (some (b false)),
               stk := Function.update (Function.update S ka rest) kb
                        (List.replicate k (e (b true)) ++ S kb) }
    ∧ Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step M)
        { l := some lc, var := v, stk := S }
        (some { l := some lnext,
                var := fpop (List.foldl (fun w y => fpop w (some y)) v
                         (List.replicate k (b true))) (some (b false)),
                stk := Function.update (Function.update S ka rest) kb
                         (List.replicate k (e (b true)) ++ S kb) })
        (k + 1))
    ∧ (Function.update (Function.update S ka rest) kb
        (List.replicate k (e (b true)) ++ S kb)) ka = rest
    ∧ (List.replicate k (e (b true)) ++ S kb).length = k + (S kb).length
    ∧ (List.replicate k (e (b true)) ++ S kb).length - (S kb).length = k := by
  sorry

end ShiTM
