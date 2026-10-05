import «AMPUNI-piece-program-semantics»

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ShiTMPieceSchedule

open ShiTMLayoutMachine

theorem run_compilePiece (n wit anc : Nat)
    (p : List Atom × List Atom) (width base : List Cell) :
    runCommands n wit anc (compilePiece p) (width, base) =
      (List.replicate (evalSum n wit anc p.1) Cell.mark ++ Cell.delim :: width,
       List.replicate (evalSum n wit anc p.2) Cell.mark ++ Cell.delim :: base) := by
  rcases p with ⟨widthAtoms, baseAtoms⟩
  simp [compilePiece, runCommands_append, runCommands, commandStep,
    run_width_atoms, run_base_atoms]

theorem compileSchedule_cons (p : List Atom × List Atom)
    (ps : List (List Atom × List Atom)) :
    compileSchedule (p :: ps) = compileSchedule ps ++ compilePiece p := by
  simp [compileSchedule, List.reverse_cons, List.map_append,
    List.flatten_append]

/-- The fixed command compiler is sound at the stack-data level: from arbitrary old
table contents, its execution prepends exactly the unary piece tables. -/
theorem run_compileSchedule (n wit anc : Nat)
    (ps : List (List Atom × List Atom)) (width base : List Cell) :
    runCommands n wit anc (compileSchedule ps) (width, base) =
      (pieceCells Prod.fst (ps.map (evalPiece n wit anc)) ++ width,
       pieceCells Prod.snd (ps.map (evalPiece n wit anc)) ++ base) := by
  induction ps generalizing width base with
  | nil => simp [compileSchedule, runCommands, pieceCells]
  | cons p ps ih =>
      rw [compileSchedule_cons, runCommands_append, ih]
      rw [run_compilePiece]
      simp [pieceCells, evalPiece, List.append_assoc]

end ShiTMPieceSchedule
