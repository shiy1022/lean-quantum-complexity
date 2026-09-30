import «AMPUNI-piece-controller-program-tables»

set_option autoImplicit false

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMPieceSchedule

theorem pieceCells_append (f : Nat × Nat → Nat)
    (ps qs : List (Nat × Nat)) :
    pieceCells f (ps ++ qs) = pieceCells f ps ++ pieceCells f qs := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp [pieceCells, ih, List.append_assoc]

/-- Since all table operations prepend, the three fixed programs must run in
reverse copy order after the final one-piece tail has been initialized. -/
theorem three_programs_table_state (n wit anc : Nat) :
    runCommands n wit anc (program 0)
      (runCommands n wit anc (program 1)
        (runCommands n wit anc (program 2)
          (pieceCells Prod.fst (copyTail n wit anc),
           pieceCells Prod.snd (copyTail n wit anc)))) =
      (pieceCells Prod.fst (ShiTMRawLayout.ampPieces n wit anc),
       pieceCells Prod.snd (ShiTMRawLayout.ampPieces n wit anc)) := by
  rw [ShiTMPieceSchedule.run_program2,
    ShiTMPieceSchedule.run_program1,
    ShiTMPieceSchedule.run_program0]
  simp [ampPieces_split, pieceCells_append, List.append_assoc]

end ShiTMPieceController
