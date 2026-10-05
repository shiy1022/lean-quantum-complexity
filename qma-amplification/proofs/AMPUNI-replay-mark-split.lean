import «AMPUNI-output-first-pass-archive-frame»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayMarkSplit

open ShiTMLayoutMachine ShiTMRetainedTop

/-- A small controller for the boundary after the first mapped circuit. The
output-index marks lie above the input-archive sentinel. Move those marks to
an otherwise empty work stack before replaying the archived input. -/
abbrev SplitLabel := Bool

abbrev archive : TopK := .inr (3 : Fin 4)
abbrev marks : TopK := .inl (.inl (0 : Fin 14))

def isMark : Sig → Bool := fun s => decide (s = some Cell.mark)

def machine : SplitLabel → Stmt TopGam SplitLabel Sig
  | false =>
      .pop archive pop
        (.branch isMark
          (.push marks get (.goto (fun _ => false)))
          (.goto (fun _ => true)))
  | true => .halt

def run : Option (Cfg TopGam SplitLabel Sig) →
    Option (Cfg TopGam SplitLabel Sig) :=
  fun c => c.bind (step machine)

/-- A mark is removed from the archive and saved on the work stack. -/
theorem mark_step (tail : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (harchive : S archive = Cell.mark :: tail) :
    run (some { l := some false, var := v, stk := S }) =
      some ⟨some false, some Cell.mark,
        Function.update (Function.update S archive tail) marks
          (Cell.mark :: S marks)⟩ := by
  simp [run, machine, step, stepAux, harchive, pop, isMark,
    ShiTMLayoutMachine.get, archive, marks]

/-- Encountering the sentinel ends the mark-moving phase. -/
theorem sentinel_step (tail : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (harchive : S archive = Cell.mirrorEnd :: tail) :
    run (some { l := some false, var := v, stk := S }) =
      some ⟨some true, some Cell.mirrorEnd,
        Function.update S archive tail⟩ := by
  simp [run, machine, step, stepAux, harchive, pop, isMark,
    archive]

end ShiTMReplayMarkSplit
