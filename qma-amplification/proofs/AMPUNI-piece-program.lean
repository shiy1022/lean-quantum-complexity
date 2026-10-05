import «AMPUNI-piece-schedule»

set_option autoImplicit false

namespace ShiTMPieceSchedule

inductive Table where
  | width | base
deriving DecidableEq, Repr

instance : Fintype Table :=
  Fintype.ofList [.width, .base]
    (by intro x; cases x <;> simp)

inductive Command where
  | delimiter (table : Table)
  | add (table : Table) (atom : Atom)
deriving DecidableEq, Repr

instance : Fintype Command :=
  Fintype.ofList
    [.delimiter .width, .delimiter .base,
     .add .width .input, .add .width .witness,
     .add .width .ancilla, .add .width .one,
     .add .base .input, .add .base .witness,
     .add .base .ancilla, .add .base .one]
    (by intro x; cases x with
      | delimiter table => cases table <;> simp
      | add table atom => cases table <;> cases atom <;> simp)

/-- Program commands are emitted in execution order. Each piece is built from its
delimiter upward, and pieces are visited in reverse because stack pushes prepend. -/
def compilePiece (p : List Atom × List Atom) : List Command :=
  [Command.delimiter .base] ++ p.2.map (Command.add .base) ++
    [Command.delimiter .width] ++ p.1.map (Command.add .width)

def compileSchedule (ps : List (List Atom × List Atom)) : List Command :=
  (ps.reverse.map compilePiece).flatten

def program (copy : Fin 3) : List Command :=
  if copy = 0 then compileSchedule copySchedule0
  else if copy = 1 then compileSchedule copySchedule1
  else compileSchedule copySchedule2

theorem program_length_le_64 (copy : Fin 3) : (program copy).length ≤ 64 := by
  fin_cases copy <;> decide

theorem program_length_pos (copy : Fin 3) : 0 < (program copy).length := by
  fin_cases copy <;> decide

end ShiTMPieceSchedule
