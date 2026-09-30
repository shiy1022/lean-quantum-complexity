import «AMPUNI-piece-tail-program»
import «AMPUNI-piece-controller-all-tables»

set_option autoImplicit false

namespace ShiTMPieceSchedule

open ShiTMLayoutMachine

/-- One fixed execution-order program: the final piece first, then copies
2, 1, and 0, since each table command prepends cells. -/
def fullProgram : List Command :=
  tailProgram ++ program 2 ++ program 1 ++ program 0

theorem fullProgram_length_le_128 : fullProgram.length ≤ 128 := by
  decide

theorem run_fullProgram (n wit anc : Nat) :
    runCommands n wit anc fullProgram ([], []) =
      (pieceCells Prod.fst (ShiTMRawLayout.ampPieces n wit anc),
       pieceCells Prod.snd (ShiTMRawLayout.ampPieces n wit anc)) := by
  rw [fullProgram, runCommands_append, runCommands_append,
    runCommands_append]
  have htail := run_tailProgram n wit anc [] []
  simp only [List.append_nil] at htail
  rw [htail]
  exact ShiTMPieceController.three_programs_table_state n wit anc

end ShiTMPieceSchedule
