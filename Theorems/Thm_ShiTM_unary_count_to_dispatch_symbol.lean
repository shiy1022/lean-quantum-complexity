-- Local reference copy of the PUBLISHED, PROVED platform theorem
-- `ShiTM.unary_count_to_dispatch_symbol`, statement verbatim, body `sorry` exactly as the
-- platform stores targets. Lets solutions cite it as a tracked reduction via
-- `import Theorems.Thm_ShiTM_unary_count_to_dispatch_symbol`. The real proof is on prove2.me.
import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace ShiTM

open Turing Turing.TM2 Turing.TM2.Stmt

theorem unary_count_to_dispatch_symbol {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Turing.TM2.Stmt Gam Lam sig) {kmark ktag : K} (hab : kmark ≠ ktag)
    {fpop : sig → Option (Gam kmark) → sig} {gmark : sig → Bool}
    (B : ℕ) (lab : ℕ → Lam) (lnext : Lam) (tagOf : ℕ → Gam ktag)
    (hM : ∀ i, i < B → M (lab i) = Turing.TM2.Stmt.pop kmark fpop
            (Turing.TM2.Stmt.branch gmark
              (Turing.TM2.Stmt.goto (fun _ => lab (i + 1)))
              (Turing.TM2.Stmt.push ktag (fun _ => tagOf i)
                (Turing.TM2.Stmt.goto (fun _ => lnext)))))
    (mark : Gam kmark) (hmark : ∀ w : sig, gmark (fpop w (some mark)) = true)
    (tl : List (Gam kmark)) (hstop : ∀ w : sig, gmark (fpop w tl.head?) = false)
    (c : ℕ) (hc : c < B) (v : sig) (S : ∀ k, List (Gam k))
    (hS : S kmark = List.replicate c mark ++ tl) :
    (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) => cf.bind (Turing.TM2.step M))^[c + 1]
        (some { l := some (lab 0), var := v, stk := S })
      = some { l := some lnext,
               var := fpop (List.foldl (fun w y => fpop w (some y)) v
                        (List.replicate c mark)) tl.head?,
               stk := Function.update (Function.update S kmark tl.tail) ktag
                        (tagOf c :: S ktag) }
    ∧ Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step M)
        { l := some (lab 0), var := v, stk := S }
        (some { l := some lnext,
                var := fpop (List.foldl (fun w y => fpop w (some y)) v
                         (List.replicate c mark)) tl.head?,
                stk := Function.update (Function.update S kmark tl.tail) ktag
                         (tagOf c :: S ktag) })
        (c + 1))
    ∧ (Function.update (Function.update S kmark tl.tail) ktag (tagOf c :: S ktag)) kmark
        = tl.tail
    ∧ (Function.update (Function.update S kmark tl.tail) ktag (tagOf c :: S ktag)) ktag
        = tagOf c :: S ktag
    ∧ ((Function.update (Function.update S kmark tl.tail) ktag
        (tagOf c :: S ktag)) ktag).head? = some (tagOf c) := by
  sorry

end ShiTM
