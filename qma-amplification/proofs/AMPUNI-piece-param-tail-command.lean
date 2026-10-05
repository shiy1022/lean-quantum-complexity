import «AMPUNI-piece-param-tail-run»
import «AMPUNI-piece-controller-frame-command»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceParam

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule
open ShiTMPieceController

theorem dispatch_field_tables (commands : List Command) (copy : Fin 3)
    (pc : PC) (atom : Atom) (table : Table) (n wit anc : Nat)
    (v : Sig) (S : ∀ k, List (TopGam k))
    (hcommand : commandAt commands pc.val = some (.add table atom))
    (hone : atom ≠ .one)
    (hsource : S (.inr (source atom)) =
      List.replicate (value n wit anc atom) Cell.mark)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)),
      (runFor commands)^[2 * value n wit anc atom + 4]
        (some { l := some (.dispatch copy pc), var := v, stk := S }) =
          some { l := some (.dispatch copy (nextPC pc)), var := none, stk := U }
      ∧ tableState U = commandStep n wit anc (.add table atom) (tableState S)
      ∧ U (.inr (source atom)) =
          List.replicate (value n wit anc atom) Cell.mark
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, j ≠ .inr (source atom) →
          j ≠ .inl (.inl (destination table)) →
          j ≠ .inl (.inl (3 : Fin 14)) → U j = S j := by
  obtain ⟨U, hrun, hsrc, hdest, hscratch', hframe⟩ :=
    ShiTMPieceParam.dispatch_field_run commands copy pc atom table
      (value n wit anc atom) v S hcommand hone hsource hscratch
  refine ⟨U, hrun, ?_, hsrc, hscratch', hframe⟩
  cases table with
  | width =>
      have hbase : U (.inl (.inl (2 : Fin 14))) =
          S (.inl (.inl (2 : Fin 14))) := by
        exact hframe _ (by simp) (by decide) (by decide)
      change
        (U (.inl (.inl (1 : Fin 14))), U (.inl (.inl (2 : Fin 14)))) =
          (List.replicate (value n wit anc atom) Cell.mark ++
            S (.inl (.inl (1 : Fin 14))), S (.inl (.inl (2 : Fin 14))))
      exact Prod.ext (by simpa [destination] using hdest) hbase
  | base =>
      have hwidth : U (.inl (.inl (1 : Fin 14))) =
          S (.inl (.inl (1 : Fin 14))) := by
        exact hframe _ (by simp) (by decide) (by decide)
      change
        (U (.inl (.inl (1 : Fin 14))), U (.inl (.inl (2 : Fin 14)))) =
          (S (.inl (.inl (1 : Fin 14))),
            List.replicate (value n wit anc atom) Cell.mark ++
              S (.inl (.inl (2 : Fin 14))))
      exact Prod.ext hwidth (by simpa [destination] using hdest)

private theorem retained_push (n wit anc : Nat)
    (S : ∀ k, List (TopGam k)) (table : Table) (cell : Cell)
    (hret : Retained n wit anc S) :
    Retained n wit anc
      (Function.update S (.inl (.inl (destination table)))
        (cell :: S (.inl (.inl (destination table))))) := by
  rcases hret with ⟨h0, h1, h2⟩
  exact ⟨by simpa [Retained] using h0,
    by simpa [Retained] using h1,
    by simpa [Retained] using h2⟩

private theorem scratch_push (S : ∀ k, List (TopGam k))
    (table : Table) (cell : Cell)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    (Function.update S (.inl (.inl (destination table)))
      (cell :: S (.inl (.inl (destination table)))))
        (.inl (.inl (3 : Fin 14))) = [] := by
  cases table <;> simpa [destination] using hscratch

private theorem retained_field (n wit anc : Nat)
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

/-- Any fixed program command has the pure table effect, preserves retained
headers and scratch, and frames all stacks outside its write set. -/
theorem dispatch_command (commands : List Command) (copy : Fin 3)
    (pc : PC) (command : Command) (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hcommand : commandAt commands pc.val = some command)
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig),
      (runFor commands)^[commandCost n wit anc command]
        (some { l := some (.dispatch copy pc), var := v, stk := S }) =
          some { l := some (.dispatch copy (nextPC pc)), var := v', stk := U }
      ∧ tableState U = commandStep n wit anc command (tableState S)
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  cases command with
  | delimiter table =>
      let U := Function.update S (.inl (.inl (destination table)))
        (Cell.delim :: S (.inl (.inl (destination table))))
      refine ⟨U, v, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [commandCost, U] using
          ShiTMPieceParam.dispatch_delimiter_step commands copy pc table v S hcommand
      · exact delimiter_table_step n wit anc table S
      · exact retained_push n wit anc S table .delim hret
      · exact scratch_push S table .delim hscratch
      · intro j hj
        simp [U, Function.update_of_ne (outside_destination j table hj)]
  | add table atom =>
      cases atom with
      | one =>
          let U := Function.update S (.inl (.inl (destination table)))
            (Cell.mark :: S (.inl (.inl (destination table))))
          refine ⟨U, v, ?_, ?_, ?_, ?_, ?_⟩
          · simpa [commandCost, U] using
              ShiTMPieceParam.dispatch_one_step commands copy pc table v S hcommand
          · exact one_table_step n wit anc table S
          · exact retained_push n wit anc S table .mark hret
          · exact scratch_push S table .mark hscratch
          · intro j hj
            simp [U, Function.update_of_ne (outside_destination j table hj)]
      | input =>
          obtain ⟨U, hrun, htable, hsrc, hscratch', hframe⟩ :=
            dispatch_field_tables commands copy pc .input table n wit anc v S
              hcommand (by decide) hret.1 hscratch
          refine ⟨U, none, by simpa [commandCost] using hrun, htable,
            retained_field n wit anc .input table S U hret hsrc hframe (by decide),
            hscratch', ?_⟩
          intro j hj
          exact hframe j (outside_source j .input hj)
            (outside_destination j table hj) (outside_scratch j hj)
      | witness =>
          obtain ⟨U, hrun, htable, hsrc, hscratch', hframe⟩ :=
            dispatch_field_tables commands copy pc .witness table n wit anc v S
              hcommand (by decide) hret.2.1 hscratch
          refine ⟨U, none, by simpa [commandCost] using hrun, htable,
            retained_field n wit anc .witness table S U hret hsrc hframe (by decide),
            hscratch', ?_⟩
          intro j hj
          exact hframe j (outside_source j .witness hj)
            (outside_destination j table hj) (outside_scratch j hj)
      | ancilla =>
          obtain ⟨U, hrun, htable, hsrc, hscratch', hframe⟩ :=
            dispatch_field_tables commands copy pc .ancilla table n wit anc v S
              hcommand (by decide) hret.2.2 hscratch
          refine ⟨U, none, by simpa [commandCost] using hrun, htable,
            retained_field n wit anc .ancilla table S U hret hsrc hframe (by decide),
            hscratch', ?_⟩
          intro j hj
          exact hframe j (outside_source j .ancilla hj)
            (outside_destination j table hj) (outside_scratch j hj)

end ShiTMPieceParam
