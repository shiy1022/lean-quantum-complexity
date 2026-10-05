import «AMPUNI-piece-controller-field-tables»

set_option autoImplicit false

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

theorem delimiter_table_step (n wit anc : Nat) (table : Table)
    (S : ∀ k, List (TopGam k)) :
    tableState (Function.update S (.inl (.inl (destination table)))
      (.delim :: S (.inl (.inl (destination table))))) =
        commandStep n wit anc (.delimiter table) (tableState S) := by
  cases table <;>
    simp [tableState, commandStep, destination]

theorem one_table_step (n wit anc : Nat) (table : Table)
    (S : ∀ k, List (TopGam k)) :
    tableState (Function.update S (.inl (.inl (destination table)))
      (.mark :: S (.inl (.inl (destination table))))) =
        commandStep n wit anc (.add table .one) (tableState S) := by
  cases table <;>
    simp [tableState, commandStep, destination, value]

end ShiTMPieceController
