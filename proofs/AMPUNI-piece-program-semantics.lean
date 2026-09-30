import «AMPUNI-piece-program»
import «AMPUNI-layout-data»

set_option autoImplicit false

namespace ShiTMPieceSchedule

open ShiTMLayoutMachine

abbrev TableState := List Cell × List Cell

def commandStep (n wit anc : Nat) : Command → TableState → TableState
  | .delimiter .width, (width, base) => (Cell.delim :: width, base)
  | .delimiter .base, (width, base) => (width, Cell.delim :: base)
  | .add .width atom, (width, base) =>
      (List.replicate (value n wit anc atom) Cell.mark ++ width, base)
  | .add .base atom, (width, base) =>
      (width, List.replicate (value n wit anc atom) Cell.mark ++ base)

def runCommands (n wit anc : Nat) : List Command → TableState → TableState
  | [], state => state
  | command :: commands, state =>
      runCommands n wit anc commands (commandStep n wit anc command state)

theorem runCommands_append (n wit anc : Nat)
    (xs ys : List Command) (state : TableState) :
    runCommands n wit anc (xs ++ ys) state =
      runCommands n wit anc ys (runCommands n wit anc xs state) := by
  induction xs generalizing state with
  | nil => rfl
  | cons command xs ih =>
      simpa [runCommands] using ih (commandStep n wit anc command state)

private theorem unary_sum_swap (a b : Nat) (tail : List Cell) :
    List.replicate b Cell.mark ++ (List.replicate a Cell.mark ++ tail) =
      List.replicate (a + b) Cell.mark ++ tail := by
  rw [← List.append_assoc, List.replicate_append_replicate, Nat.add_comm]

theorem run_width_atoms (n wit anc : Nat) (xs : List Atom)
    (width base : List Cell) :
    runCommands n wit anc (xs.map (Command.add .width)) (width, base) =
      (List.replicate (evalSum n wit anc xs) Cell.mark ++ width, base) := by
  induction xs generalizing width with
  | nil => simp [runCommands, evalSum]
  | cons atom xs ih =>
      simp only [List.map_cons, runCommands, commandStep]
      rw [ih]
      change
        (List.replicate (evalSum n wit anc xs) Cell.mark ++
          (List.replicate (value n wit anc atom) Cell.mark ++ width), base) =
        (List.replicate (value n wit anc atom + evalSum n wit anc xs)
          Cell.mark ++ width, base)
      exact Prod.ext (unary_sum_swap _ _ _) rfl

theorem run_base_atoms (n wit anc : Nat) (xs : List Atom)
    (width base : List Cell) :
    runCommands n wit anc (xs.map (Command.add .base)) (width, base) =
      (width, List.replicate (evalSum n wit anc xs) Cell.mark ++ base) := by
  induction xs generalizing base with
  | nil => simp [runCommands, evalSum]
  | cons atom xs ih =>
      simp only [List.map_cons, runCommands, commandStep]
      rw [ih]
      change
        (width, List.replicate (evalSum n wit anc xs) Cell.mark ++
          (List.replicate (value n wit anc atom) Cell.mark ++ base)) =
        (width, List.replicate (value n wit anc atom + evalSum n wit anc xs)
          Cell.mark ++ base)
      exact Prod.ext rfl (unary_sum_swap _ _ _)

end ShiTMPieceSchedule
