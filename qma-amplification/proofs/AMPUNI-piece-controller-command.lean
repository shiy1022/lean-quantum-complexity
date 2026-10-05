import «AMPUNI-piece-controller-direct-tables»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

def Retained (n wit anc : Nat) (S : ∀ k, List (TopGam k)) : Prop :=
  S (.inr (0 : Fin 4)) = List.replicate n Cell.mark ∧
  S (.inr (1 : Fin 4)) = List.replicate wit Cell.mark ∧
  S (.inr (2 : Fin 4)) = List.replicate anc Cell.mark

def commandCost (n wit anc : Nat) : Command → Nat
  | .delimiter _ => 1
  | .add _ .one => 1
  | .add _ atom => 2 * value n wit anc atom + 4

private theorem retained_update_layout (n wit anc : Nat)
    (S : ∀ k, List (TopGam k)) (table : Table) (cell : Cell)
    (hret : Retained n wit anc S) :
    Retained n wit anc
      (Function.update S (.inl (.inl (destination table)))
        (cell :: S (.inl (.inl (destination table))))) := by
  rcases hret with ⟨h0, h1, h2⟩
  exact ⟨by simpa [Retained] using h0,
    by simpa [Retained] using h1,
    by simpa [Retained] using h2⟩

private theorem scratch_update_layout (S : ∀ k, List (TopGam k))
    (table : Table) (cell : Cell)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    (Function.update S (.inl (.inl (destination table)))
      (cell :: S (.inl (.inl (destination table)))))
        (.inl (.inl (3 : Fin 14))) = [] := by
  cases table <;> simpa [destination] using hscratch

private theorem retained_of_field (n wit anc : Nat)
    (atom : Atom) (table : Table)
    (S U : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (hsrc : U (.inr (source atom)) =
      List.replicate (value n wit anc atom) Cell.mark)
    (hframe : ∀ j, j ≠ .inr (source atom) →
      j ≠ .inl (.inl (destination table)) →
      j ≠ .inl (.inl (3 : Fin 14)) → U j = S j)
    (hone : atom ≠ .one) : Retained n wit anc U := by
  rcases hret with ⟨h0, h1, h2⟩
  cases atom with
  | input =>
      refine ⟨by simpa [source, value] using hsrc, ?_, ?_⟩
      · rw [hframe (.inr (1 : Fin 4)) (by simp [source]) (by simp) (by simp)]
        exact h1
      · rw [hframe (.inr (2 : Fin 4)) (by simp [source]) (by simp) (by simp)]
        exact h2
  | witness =>
      refine ⟨?_, by simpa [source, value] using hsrc, ?_⟩
      · rw [hframe (.inr (0 : Fin 4)) (by simp [source]) (by simp) (by simp)]
        exact h0
      · rw [hframe (.inr (2 : Fin 4)) (by simp [source]) (by simp) (by simp)]
        exact h2
  | ancilla =>
      refine ⟨?_, ?_, by simpa [source, value] using hsrc⟩
      · rw [hframe (.inr (0 : Fin 4)) (by simp [source]) (by simp) (by simp)]
        exact h0
      · rw [hframe (.inr (1 : Fin 4)) (by simp [source]) (by simp) (by simp)]
        exact h1
  | one => exact (hone rfl).elim

/-- One command makes its specified table-state update and preserves the
retained headers and empty scratch. The final variable value is existential
because direct pushes preserve it while a copy/restore command clears it. -/
theorem dispatch_command (copy : Fin 3) (pc : PC)
    (command : Command) (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hcommand : commandAt (program copy) pc.val = some command)
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig),
      run^[commandCost n wit anc command]
        (some { l := some (.dispatch copy pc), var := v, stk := S }) =
          some { l := some (.dispatch copy (nextPC pc)), var := v', stk := U }
      ∧ tableState U = commandStep n wit anc command (tableState S)
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = [] := by
  cases command with
  | delimiter table =>
      let U := Function.update S (.inl (.inl (destination table)))
        (.delim :: S (.inl (.inl (destination table))))
      refine ⟨U, v, ?_, ?_, ?_, ?_⟩
      · simpa [commandCost, U] using
          dispatch_delimiter_step copy pc table v S hcommand
      · exact delimiter_table_step n wit anc table S
      · exact retained_update_layout n wit anc S table .delim hret
      · exact scratch_update_layout S table .delim hscratch
  | add table atom =>
      cases atom with
      | one =>
          let U := Function.update S (.inl (.inl (destination table)))
            (.mark :: S (.inl (.inl (destination table))))
          refine ⟨U, v, ?_, ?_, ?_, ?_⟩
          · simpa [commandCost, U] using
              dispatch_one_step copy pc table v S hcommand
          · exact one_table_step n wit anc table S
          · exact retained_update_layout n wit anc S table .mark hret
          · exact scratch_update_layout S table .mark hscratch
      | input =>
          obtain ⟨U, hrun, htable, hsrc, hscratch', hframe⟩ :=
            dispatch_field_tables copy pc .input table n wit anc v S
              hcommand (by decide) hret.1 hscratch
          exact ⟨U, none, by simpa [commandCost] using hrun, htable,
            retained_of_field n wit anc .input table S U hret hsrc hframe (by decide),
            hscratch'⟩
      | witness =>
          obtain ⟨U, hrun, htable, hsrc, hscratch', hframe⟩ :=
            dispatch_field_tables copy pc .witness table n wit anc v S
              hcommand (by decide) hret.2.1 hscratch
          exact ⟨U, none, by simpa [commandCost] using hrun, htable,
            retained_of_field n wit anc .witness table S U hret hsrc hframe (by decide),
            hscratch'⟩
      | ancilla =>
          obtain ⟨U, hrun, htable, hsrc, hscratch', hframe⟩ :=
            dispatch_field_tables copy pc .ancilla table n wit anc v S
              hcommand (by decide) hret.2.2 hscratch
          exact ⟨U, none, by simpa [commandCost] using hrun, htable,
            retained_of_field n wit anc .ancilla table S U hret hsrc hframe (by decide),
            hscratch'⟩

end ShiTMPieceController
