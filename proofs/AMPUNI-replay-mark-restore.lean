import «AMPUNI-replay-reload-full-run»
import «AMPUNI-replay-mark-split-handoff»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayMarkRestore

open ShiTMLayoutMachine ShiTMRetainedTop

/-- After reloading the input, put the output-index marks back above the
archive sentinel. This empties stack 0, which the circuit parser uses as
scratch. -/
abbrev RestoreLabel := Bool

abbrev archive : TopK := .inr (3 : Fin 4)
abbrev marks : TopK := .inl (.inl (0 : Fin 14))

def machine : RestoreLabel → Stmt TopGam RestoreLabel Sig
  | false =>
      .pop marks pop
        (.branch isSome
          (.push archive get (.goto (fun _ => false)))
          (.goto (fun _ => true)))
  | true => .halt

def run : Option (Cfg TopGam RestoreLabel Sig) →
    Option (Cfg TopGam RestoreLabel Sig) :=
  fun c => c.bind (step machine)

theorem mark_step (tail : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (hmarks : S marks = Cell.mark :: tail) :
    run (some { l := some false, var := v, stk := S }) =
      some ⟨some false, some Cell.mark,
        Function.update (Function.update S marks tail) archive
          (Cell.mark :: S archive)⟩ := by
  simp [run, machine, step, stepAux, hmarks, pop, isSome,
    ShiTMLayoutMachine.get, marks, archive]

theorem empty_step (v : Sig) (S : ∀ k, List (TopGam k))
    (hmarks : S marks = []) :
    run (some { l := some false, var := v, stk := S }) =
      some ⟨some true, none, Function.update S marks []⟩ := by
  simp [run, machine, step, stepAux, hmarks, pop, isSome]

end ShiTMReplayMarkRestore
