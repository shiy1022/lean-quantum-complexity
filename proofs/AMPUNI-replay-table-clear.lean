import «AMPUNI-replay-mark-restore-run»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayTableClear

open ShiTMLayoutMachine ShiTMRetainedTop

/-- Clear the two old piece tables and their two mirrors. The numeric retained
headers, archived input, source, output accumulator, and delimiter are never
targeted. -/
inductive Phase where
  | width | base | widthMirror | baseMirror | done
deriving DecidableEq

def target : Phase → Fin 14
  | .width => 1
  | .base => 2
  | .widthMirror => 8
  | .baseMirror => 9
  | .done => 1

abbrev stack (p : Phase) : TopK := .inl (.inl (target p))

def next : Phase → Phase
  | .width => .base
  | .base => .widthMirror
  | .widthMirror => .baseMirror
  | .baseMirror => .done
  | .done => .done

def machine : Phase → Stmt TopGam Phase Sig
  | .done => .halt
  | p =>
      .pop (stack p) pop
        (.branch isSome
          (.goto (fun _ => p))
          (.goto (fun _ => next p)))

def run : Option (Cfg TopGam Phase Sig) →
    Option (Cfg TopGam Phase Sig) :=
  fun c => c.bind (step machine)

theorem cell_step (p : Phase) (hp : p ≠ .done)
    (c : Cell) (tail : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (htarget : S (stack p) = c :: tail) :
    run (some { l := some p, var := v, stk := S }) =
      some ⟨some p, some c, Function.update S (stack p) tail⟩ := by
  cases p <;> simp_all [run, machine, target, next, step, stepAux,
    stack, htarget, pop, isSome]

theorem empty_step (p : Phase) (hp : p ≠ .done)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (htarget : S (stack p) = []) :
    run (some { l := some p, var := v, stk := S }) =
      some ⟨some (next p), none, Function.update S (stack p) []⟩ := by
  cases p <;> simp_all [run, machine, target, next, step, stepAux,
    stack, htarget, pop, isSome]

end ShiTMReplayTableClear
