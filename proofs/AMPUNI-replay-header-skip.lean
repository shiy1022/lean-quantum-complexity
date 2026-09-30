import «AMPUNI-retained-header-run»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayHeaderSkip

open ShiTMLayoutMachine ShiTMRetainedTop

/-- Four unary headers are traversed without writing the retained counts.
The source is then positioned at the circuit encoding for a replay pass. -/
abbrev Phase := Fin 5

abbrev source : TopK := .inl (.inl (11 : Fin 14))

def next : Phase → Phase
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | _ => 4

def machine (p : Phase) : Stmt TopGam Phase Sig :=
  if p = 4 then .halt else
    .pop source pop
      (.branch isSome
        (.branch isMark
          (.goto (fun _ => p))
          (.goto (fun _ => next p)))
        .halt)

def run : Option (Cfg TopGam Phase Sig) →
    Option (Cfg TopGam Phase Sig) :=
  fun c => c.bind (step machine)

theorem mark_step (p : Phase) (hp : p ≠ 4)
    (v : Sig) (S : ∀ k, List (TopGam k)) (tail : List Cell)
    (hsrc : S source = Cell.mark :: tail) :
    run (some ⟨some p, v, S⟩) =
      some ⟨some p, some Cell.mark, Function.update S source tail⟩ := by
  simp [run, machine, hp, step, stepAux, hsrc,
    source, pop, isSome, isMark]

theorem delim_step (p : Phase) (hp : p ≠ 4)
    (v : Sig) (S : ∀ k, List (TopGam k)) (tail : List Cell)
    (hsrc : S source = Cell.delim :: tail) :
    run (some ⟨some p, v, S⟩) =
      some ⟨some (next p), some Cell.delim,
        Function.update S source tail⟩ := by
  simp [run, machine, hp, step, stepAux, hsrc,
    source, pop, isSome, isMark]

end ShiTMReplayHeaderSkip
