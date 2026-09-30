import «AMPUNI-piece-program-correct»

set_option autoImplicit false

namespace ShiTMPieceSchedule

open ShiTMLayoutMachine

/-- The terminal one-wire piece of the full amplification layout. Its base is
three copies of each retained unary header plus three constant marks. -/
def tailSchedule : List (List Atom × List Atom) :=
  [([.one],
    [.input, .input, .input,
     .witness, .witness, .witness,
     .ancilla, .ancilla, .ancilla,
     .one, .one, .one])]

def tailProgram : List Command := compileSchedule tailSchedule

theorem tailProgram_length_le_64 : tailProgram.length ≤ 64 := by
  decide

theorem eval_tailSchedule (n wit anc : Nat) :
    tailSchedule.map (evalPiece n wit anc) = copyTail n wit anc := by
  simp [tailSchedule, evalPiece, evalSum, value, copyTail] <;> omega

theorem run_tailProgram (n wit anc : Nat) (width base : List Cell) :
    runCommands n wit anc tailProgram (width, base) =
      (pieceCells Prod.fst (copyTail n wit anc) ++ width,
       pieceCells Prod.snd (copyTail n wit anc) ++ base) := by
  simpa [tailProgram, eval_tailSchedule] using
    (run_compileSchedule n wit anc tailSchedule width base)

end ShiTMPieceSchedule
