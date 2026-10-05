import «AMPUNI-piece-controller-command»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMPieceController

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceSchedule

/-- The only stacks a piece command can touch are the two table stacks,
scratch stack 3, and the three retained unary sources. -/
def OutsideWrites (j : TopK) : Prop :=
  j ≠ .inl (.inl (1 : Fin 14)) ∧
  j ≠ .inl (.inl (2 : Fin 14)) ∧
  j ≠ .inl (.inl (3 : Fin 14)) ∧
  j ≠ .inr (0 : Fin 4) ∧
  j ≠ .inr (1 : Fin 4) ∧
  j ≠ .inr (2 : Fin 4)

theorem outside_destination (j : TopK) (table : Table)
    (hj : OutsideWrites j) :
    j ≠ .inl (.inl (destination table)) := by
  rcases hj with ⟨h1, h2, _, _, _, _⟩
  cases table with
  | width => simpa [destination] using h1
  | base => simpa [destination] using h2

theorem outside_source (j : TopK) (atom : Atom)
    (hj : OutsideWrites j) : j ≠ .inr (source atom) := by
  rcases hj with ⟨_, _, _, h0, h1, h2⟩
  cases atom with
  | input => simpa [source] using h0
  | witness => simpa [source] using h1
  | ancilla => simpa [source] using h2
  | one => simpa [source] using h0

theorem outside_scratch (j : TopK) (hj : OutsideWrites j) :
    j ≠ .inl (.inl (3 : Fin 14)) := hj.2.2.1

/-- A single scheduled command has an exact frame outside its write set. -/
theorem dispatch_command_frame (copy : Fin 3) (pc : PC)
    (command : Command) (n wit anc : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hcommand : commandAt (program copy) pc.val = some command)
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig),
      run^[commandCost n wit anc command]
        (some { l := some (.dispatch copy pc), var := v, stk := S }) =
          some { l := some (.dispatch copy (nextPC pc)), var := v', stk := U }
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  cases command with
  | delimiter table =>
      let U := Function.update S (.inl (.inl (destination table)))
        (Cell.delim :: S (.inl (.inl (destination table))))
      refine ⟨U, v, ?_, ?_⟩
      · simpa [commandCost, U] using
          dispatch_delimiter_step copy pc table v S hcommand
      · intro j hj
        simp [U, Function.update_of_ne (outside_destination j table hj)]
  | add table atom =>
      cases atom with
      | one =>
          let U := Function.update S (.inl (.inl (destination table)))
            (Cell.mark :: S (.inl (.inl (destination table))))
          refine ⟨U, v, ?_, ?_⟩
          · simpa [commandCost, U] using
              dispatch_one_step copy pc table v S hcommand
          · intro j hj
            simp [U, Function.update_of_ne (outside_destination j table hj)]
      | input =>
          obtain ⟨U, hrun, _, _, _, hframe⟩ :=
            dispatch_field_tables copy pc .input table n wit anc v S
              hcommand (by decide) hret.1 hscratch
          refine ⟨U, none, by simpa [commandCost] using hrun, ?_⟩
          intro j hj
          exact hframe j (outside_source j .input hj)
            (outside_destination j table hj) (outside_scratch j hj)
      | witness =>
          obtain ⟨U, hrun, _, _, _, hframe⟩ :=
            dispatch_field_tables copy pc .witness table n wit anc v S
              hcommand (by decide) hret.2.1 hscratch
          refine ⟨U, none, by simpa [commandCost] using hrun, ?_⟩
          intro j hj
          exact hframe j (outside_source j .witness hj)
            (outside_destination j table hj) (outside_scratch j hj)
      | ancilla =>
          obtain ⟨U, hrun, _, _, _, hframe⟩ :=
            dispatch_field_tables copy pc .ancilla table n wit anc v S
              hcommand (by decide) hret.2.2 hscratch
          refine ⟨U, none, by simpa [commandCost] using hrun, ?_⟩
          intro j hj
          exact hframe j (outside_source j .ancilla hj)
            (outside_destination j table hj) (outside_scratch j hj)

end ShiTMPieceController
