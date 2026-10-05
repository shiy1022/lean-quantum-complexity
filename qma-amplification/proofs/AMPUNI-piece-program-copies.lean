import «AMPUNI-piece-program-correct»

set_option autoImplicit false

namespace ShiTMPieceSchedule

open ShiTMLayoutMachine

/-- Each fixed piece program emits the width and base stacks already specified
for its corresponding amplification copy. -/
theorem run_program0 (n wit anc : Nat) (width base : List Cell) :
    runCommands n wit anc (program 0) (width, base) =
      (pieceCells Prod.fst (copyPieces0 n wit anc) ++ width,
       pieceCells Prod.snd (copyPieces0 n wit anc) ++ base) := by
  simpa [program, eval_copySchedule0] using
    (run_compileSchedule n wit anc copySchedule0 width base)

theorem run_program1 (n wit anc : Nat) (width base : List Cell) :
    runCommands n wit anc (program 1) (width, base) =
      (pieceCells Prod.fst (copyPieces1 n wit anc) ++ width,
       pieceCells Prod.snd (copyPieces1 n wit anc) ++ base) := by
  simpa [program, eval_copySchedule1] using
    (run_compileSchedule n wit anc copySchedule1 width base)

theorem run_program2 (n wit anc : Nat) (width base : List Cell) :
    runCommands n wit anc (program 2) (width, base) =
      (pieceCells Prod.fst (copyPieces2 n wit anc) ++ width,
       pieceCells Prod.snd (copyPieces2 n wit anc) ++ base) := by
  simpa [program, eval_copySchedule2] using
    (run_compileSchedule n wit anc copySchedule2 width base)

end ShiTMPieceSchedule
