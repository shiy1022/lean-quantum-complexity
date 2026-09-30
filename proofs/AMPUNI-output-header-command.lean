import «AMPUNI-output-header-work-run»
import «AMPUNI-output-header-bounds»
import «AMPUNI-piece-controller-command»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMOutputHeader

open ShiTMLayoutMachine ShiTMRetainedTop ShiTMPieceController

def OutsideWrites (j : TopK) : Prop :=
  j ≠ .inl (.inl (13 : Fin 14)) ∧
  j ≠ .inl (.inl (3 : Fin 14)) ∧
  j ≠ .inr (0 : Fin 4) ∧
  j ≠ .inr (1 : Fin 4) ∧
  j ≠ .inr (2 : Fin 4)

private theorem outside_source (j : TopK) (atom : Atom)
    (hj : OutsideWrites j) : j ≠ .inr (source atom) := by
  cases atom with
  | input => exact hj.2.2.1
  | witness => exact hj.2.2.2.1
  | ancilla => exact hj.2.2.2.2
  | one => exact hj.2.2.1

private theorem retained_of_field (n wit anc : Nat) (atom : Atom)
    (S U : ∀ k, List (TopGam k))
    (hret : Retained n wit anc S)
    (hsrc : U (.inr (source atom)) =
      List.replicate (value n wit anc atom) Cell.mark)
    (hframe : ∀ j, j ≠ .inr (source atom) →
      j ≠ .inl (.inl (13 : Fin 14)) →
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

theorem dispatch_command (pc : PC) (command : Command)
    (n wit anc : Nat) (v : Sig) (S : ∀ k, List (TopGam k))
    (hcommand : commandAt program pc.val = some command)
    (hret : Retained n wit anc S)
    (hscratch : S (.inl (.inl (3 : Fin 14))) = []) :
    ∃ (U : ∀ k, List (TopGam k)) (v' : Sig),
      run^[commandCost n wit anc command]
        (some { l := some (.dispatch pc), var := v, stk := S }) =
          some { l := some (.dispatch (nextPC pc)), var := v', stk := U }
      ∧ U (.inl (.inl (13 : Fin 14))) =
          cells n wit anc command ++ S (.inl (.inl (13 : Fin 14)))
      ∧ Retained n wit anc U
      ∧ U (.inl (.inl (3 : Fin 14))) = []
      ∧ ∀ j, OutsideWrites j → U j = S j := by
  cases command with
  | delimiter =>
      let U := Function.update S (.inl (.inl (13 : Fin 14)))
        (Cell.delim :: S (.inl (.inl (13 : Fin 14))))
      refine ⟨U, v, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [commandCost, U, pushOut] using dispatch_delimiter_step pc v S hcommand
      · simp [U, cells]
      · rcases hret with ⟨h0, h1, h2⟩
        exact ⟨by simpa [U] using h0, by simpa [U] using h1,
          by simpa [U] using h2⟩
      · simpa [U] using hscratch
      · intro j hj
        simp [U, Function.update_of_ne hj.1]
  | add atom =>
      cases atom with
      | one =>
          let U := Function.update S (.inl (.inl (13 : Fin 14)))
            (Cell.mark :: S (.inl (.inl (13 : Fin 14))))
          refine ⟨U, v, ?_, ?_, ?_, ?_, ?_⟩
          · simpa [commandCost, U, pushOut] using dispatch_one_step pc v S hcommand
          · simp [U, cells, value]
          · rcases hret with ⟨h0, h1, h2⟩
            exact ⟨by simpa [U] using h0, by simpa [U] using h1,
              by simpa [U] using h2⟩
          · simpa [U] using hscratch
          · intro j hj
            simp [U, Function.update_of_ne hj.1]
      | input =>
          obtain ⟨U, hr, hs, ho, hsc, hf⟩ :=
            dispatch_field_run pc .input n v S hcommand (by decide)
              hret.1 hscratch
          exact ⟨U, none, by simpa [commandCost, value] using hr,
            by simpa [cells, value] using ho,
            retained_of_field n wit anc .input S U hret
              (by simpa [value] using hs) hf (by decide), hsc,
            by intro j hj; exact hf j (outside_source j .input hj) hj.1 hj.2.1⟩
      | witness =>
          obtain ⟨U, hr, hs, ho, hsc, hf⟩ :=
            dispatch_field_run pc .witness wit v S hcommand (by decide)
              hret.2.1 hscratch
          exact ⟨U, none, by simpa [commandCost, value] using hr,
            by simpa [cells, value] using ho,
            retained_of_field n wit anc .witness S U hret
              (by simpa [value] using hs) hf (by decide), hsc,
            by intro j hj; exact hf j (outside_source j .witness hj) hj.1 hj.2.1⟩
      | ancilla =>
          obtain ⟨U, hr, hs, ho, hsc, hf⟩ :=
            dispatch_field_run pc .ancilla anc v S hcommand (by decide)
              hret.2.2 hscratch
          exact ⟨U, none, by simpa [commandCost, value] using hr,
            by simpa [cells, value] using ho,
            retained_of_field n wit anc .ancilla S U hret
              (by simpa [value] using hs) hf (by decide), hsc,
            by intro j hj; exact hf j (outside_source j .ancilla hj) hj.1 hj.2.1⟩

end ShiTMOutputHeader
