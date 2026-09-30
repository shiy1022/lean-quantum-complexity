import «AMPUNI-replay-mark-split-run»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMReplayReload

open ShiTMLayoutMachine ShiTMRetainedTop

/-- Phase 0 transfers the reversed archive to the source, also saving each
cell on scratch. Phase 1 restores scratch to the archive. Phase 2 hands off
to the next circuit pass. -/
abbrev ReloadLabel := Fin 3

abbrev source : TopK := .inl (.inl (11 : Fin 14))
abbrev scratch : TopK := .inl (.inl (3 : Fin 14))
abbrev archive : TopK := .inr (3 : Fin 4)

def machine : ReloadLabel → Stmt TopGam ReloadLabel Sig
  | 0 =>
      .pop archive pop
        (.branch isSome
          (.push source get
            (.push scratch get (.goto (fun _ => 0))))
          (.goto (fun _ => 1)))
  | 1 =>
      .pop scratch pop
        (.branch isSome
          (.push archive get (.goto (fun _ => 1)))
          (.push archive (cst .mirrorEnd) (.goto (fun _ => 2))))
  | _ => .halt

def run : Option (Cfg TopGam ReloadLabel Sig) →
    Option (Cfg TopGam ReloadLabel Sig) :=
  fun c => c.bind (step machine)

/-- Each transfer cell advances the source and scratch together. -/
theorem transfer_cell_step (c : Cell) (tail : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (harchive : S archive = c :: tail) :
    run (some { l := some 0, var := v, stk := S }) =
      some ⟨some 0, some c,
        Function.update
          (Function.update (Function.update S archive tail) source
            (c :: S source)) scratch (c :: S scratch)⟩ := by
  simp [run, machine, step, stepAux, harchive, pop, isSome,
    ShiTMLayoutMachine.get, archive, source, scratch]

theorem transfer_empty_step (v : Sig) (S : ∀ k, List (TopGam k))
    (harchive : S archive = []) :
    run (some { l := some 0, var := v, stk := S }) =
      some ⟨some 1, none, Function.update S archive []⟩ := by
  simp [run, machine, step, stepAux, harchive, pop, isSome]

/-- Each restore cell rebuilds the original reversed archive. -/
theorem restore_cell_step (c : Cell) (tail : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (hscratch : S scratch = c :: tail) :
    run (some { l := some 1, var := v, stk := S }) =
      some ⟨some 1, some c,
        Function.update (Function.update S scratch tail) archive
          (c :: S archive)⟩ := by
  simp [run, machine, step, stepAux, hscratch, pop, isSome,
    ShiTMLayoutMachine.get, scratch, archive]

/-- Once scratch is empty, replace the sentinel below the saved input. -/
theorem restore_empty_step (v : Sig) (S : ∀ k, List (TopGam k))
    (hscratch : S scratch = []) :
    run (some { l := some 1, var := v, stk := S }) =
      some ⟨some 2, none,
        Function.update (Function.update S scratch []) archive
          (Cell.mirrorEnd :: S archive)⟩ := by
  simp [run, machine, step, stepAux, hscratch, pop, isSome,
    scratch, archive, cst]

end ShiTMReplayReload
