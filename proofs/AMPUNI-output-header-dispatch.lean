import «AMPUNI-output-header-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMOutputHeader

open ShiTMLayoutMachine ShiTMRetainedTop

def pushOut (c : Cell) (S : ∀ k, List (TopGam k)) :
    ∀ k, List (TopGam k) :=
  Function.update S (.inl (.inl (13 : Fin 14)))
    (c :: S (.inl (.inl (13 : Fin 14))))

theorem dispatch_delimiter_step (pc : PC) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hc : commandAt program pc.val = some .delimiter) :
    run^[1] (some { l := some (.dispatch pc), var := v, stk := S }) =
      some { l := some (.dispatch (nextPC pc)), var := v, stk := pushOut .delim S } := by
  simp [run, machine, hc, step, stepAux, cst, pushOut]

theorem dispatch_one_step (pc : PC) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hc : commandAt program pc.val = some (.add .one)) :
    run^[1] (some { l := some (.dispatch pc), var := v, stk := S }) =
      some { l := some (.dispatch (nextPC pc)), var := v, stk := pushOut .mark S } := by
  simp [run, machine, hc, step, stepAux, cst, pushOut]

theorem dispatch_field_step (pc : PC) (atom : Atom) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hc : commandAt program pc.val = some (.add atom))
    (hone : atom ≠ .one) :
    run^[1] (some { l := some (.dispatch pc), var := v, stk := S }) =
      some { l := some (.work pc atom .copy), var := v, stk := S } := by
  cases atom <;> simp_all [run, machine, step, stepAux]

theorem work_done_step (pc : PC) (atom : Atom) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run^[1] (some { l := some (.work pc atom .done), var := v, stk := S }) =
      some { l := some (.dispatch (nextPC pc)), var := v, stk := S } := by
  simp [run, machine, step, stepAux]

theorem terminal_dispatch_step (pc : PC) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hc : commandAt program pc.val = none) :
    run^[1] (some { l := some (.dispatch pc), var := v, stk := S }) =
      some { l := some .finished, var := v, stk := S } := by
  simp [run, machine, hc, step, stepAux]

end ShiTMOutputHeader
