import «AMPUNI-mirror-init-machine»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMMirrorInit

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

def sourceIndex : Table → Fin 14
  | .width => 1
  | .base => 2

def mirrorIndex : Table → Fin 14
  | .width => 8
  | .base => 9

def startPhase : Table → Phase
  | .width => .startWidth
  | .base => .startBase

def copyPhase : Table → Phase
  | .width => .copyWidth
  | .base => .copyBase

def restorePhase : Table → Phase
  | .width => .restoreWidth
  | .base => .restoreBase

def nextPhase : Table → Phase
  | .width => .startBase
  | .base => .done

theorem start_step (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k)) :
    run^[1] (some { l := some (startPhase table), var := v, stk := S }) =
      some { l := some (copyPhase table), var := v, stk :=
        (Function.update S (.inl (.inl (mirrorIndex table)))
          (.mirrorEnd :: S (.inl (.inl (mirrorIndex table))))) } := by
  cases table <;> simp [run, machine, startPhase, copyPhase,
    mirrorIndex, step, stepAux, cst]

theorem copy_cell_step (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k)) (cell : Cell) (tail : List Cell)
    (hsrc : S (.inl (.inl (sourceIndex table))) = cell :: tail) :
    run^[1] (some { l := some (copyPhase table), var := v, stk := S }) =
      some { l := some (copyPhase table), var := some cell, stk :=
        (Function.update
          (Function.update
            (Function.update S (.inl (.inl (sourceIndex table))) tail)
            (.inl (.inl (mirrorIndex table)))
              (cell :: S (.inl (.inl (mirrorIndex table)))))
          (.inl (.inl (10 : Fin 14)))
            (cell :: S (.inl (.inl (10 : Fin 14))))) } := by
  cases table with
  | width =>
      have h : S (.inl (.inl (1 : Fin 14))) = cell :: tail := by
        simpa [sourceIndex] using hsrc
      simp [run, machine, copyPhase, sourceIndex, mirrorIndex,
        step, stepAux, h, pop, isSome, ShiTMLayoutMachine.get]
  | base =>
      have h : S (.inl (.inl (2 : Fin 14))) = cell :: tail := by
        simpa [sourceIndex] using hsrc
      simp [run, machine, copyPhase, sourceIndex, mirrorIndex,
        step, stepAux, h, pop, isSome, ShiTMLayoutMachine.get]

theorem copy_empty_step (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hsrc : S (.inl (.inl (sourceIndex table))) = []) :
    run^[1] (some { l := some (copyPhase table), var := v, stk := S }) =
      some { l := some (restorePhase table), var := none, stk := S } := by
  cases table with
  | width =>
      have h : S (.inl (.inl (1 : Fin 14))) = [] := by
        simpa [sourceIndex] using hsrc
      simp [run, machine, copyPhase, restorePhase,
        sourceIndex, step, stepAux, h, pop, isSome]
  | base =>
      have h : S (.inl (.inl (2 : Fin 14))) = [] := by
        simpa [sourceIndex] using hsrc
      simp [run, machine, copyPhase, restorePhase,
        sourceIndex, step, stepAux, h, pop, isSome]

theorem restore_cell_step (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k)) (cell : Cell) (tail : List Cell)
    (hscratch : S (.inl (.inl (10 : Fin 14))) = cell :: tail) :
    run^[1] (some { l := some (restorePhase table), var := v, stk := S }) =
      some { l := some (restorePhase table), var := some cell, stk :=
        (Function.update
          (Function.update S (.inl (.inl (10 : Fin 14))) tail)
          (.inl (.inl (sourceIndex table)))
            (cell :: S (.inl (.inl (sourceIndex table))))) } := by
  cases table <;> simp [run, machine, restorePhase, sourceIndex,
    step, stepAux, hscratch, pop, isSome, ShiTMLayoutMachine.get]

theorem restore_empty_step (table : Table) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hscratch : S (.inl (.inl (10 : Fin 14))) = []) :
    run^[1] (some { l := some (restorePhase table), var := v, stk := S }) =
      some { l := some (nextPhase table), var := none, stk := S } := by
  cases table <;> simp [run, machine, restorePhase, nextPhase,
    step, stepAux, hscratch, pop, isSome]

end ShiTMMirrorInit
