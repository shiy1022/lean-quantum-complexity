import «AMPUNI-replay-mark-split»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayMarkSplit

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

private theorem marks_commute (n : Nat) (s : List Cell) :
    List.replicate n Cell.mark ++ Cell.mark :: s =
      Cell.mark :: (List.replicate n Cell.mark ++ s) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using congrArg (List.cons Cell.mark) ih

/-- All output-index marks can be stripped without touching the archived
input below the sentinel. The cost is exactly one step per mark plus the
sentinel step. -/
theorem split_all_run (count : Nat) (input : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (harchive : S archive =
      List.replicate count Cell.mark ++ Cell.mirrorEnd :: input) :
    ∃ U : ∀ k, List (TopGam k),
      run^[count + 1]
        (some { l := some false, var := v, stk := S }) =
          some { l := some true, var := some Cell.mirrorEnd, stk := U }
      ∧ U archive = input
      ∧ U marks = List.replicate count Cell.mark ++ S marks
      ∧ ∀ j : TopK, j ≠ archive → j ≠ marks → U j = S j := by
  induction count generalizing v S with
  | zero =>
      let U := Function.update S archive input
      refine ⟨U, ?_, ?_, ?_, ?_⟩
      · simpa [U] using sentinel_step input v S (by simpa using harchive)
      · simp [U]
      · simp [U, Function.update_of_ne (show marks ≠ archive by decide)]
      · intro j hj _
        exact Function.update_of_ne hj _ _
  | succ count ih =>
      let T : ∀ k : TopK, List (TopGam k) :=
        Function.update
          (Function.update S archive
            (List.replicate count Cell.mark ++ Cell.mirrorEnd :: input))
          marks (Cell.mark :: S marks)
      have hTarchive : T archive =
          List.replicate count Cell.mark ++ Cell.mirrorEnd :: input := by
        simp [T, Function.update_of_ne (show archive ≠ marks by decide)]
      have hhead : S archive =
          Cell.mark :: (List.replicate count Cell.mark ++ Cell.mirrorEnd :: input) := by
        simpa [List.replicate_succ] using harchive
      obtain ⟨U, hrun, hUarchive, hUmarks, hUframe⟩ :=
        ih (some Cell.mark) T hTarchive
      refine ⟨U, ?_, hUarchive, ?_, ?_⟩
      · have hfirst : run^[1]
            (some { l := some false, var := v, stk := S }) =
              some { l := some false, var := some Cell.mark, stk := T } := by
          simpa [T, Function.iterate_succ_apply'] using
            mark_step (List.replicate count Cell.mark ++ Cell.mirrorEnd :: input)
              v S hhead
        rw [show count.succ + 1 = 1 + (count + 1) by omega]
        exact iterTwo run 1 (count + 1) _ _ _ hfirst hrun
      · rw [hUmarks]
        simp only [T, Function.update_self]
        simpa [List.replicate_succ] using marks_commute count (S marks)
      · intro j hj0 hj1
        rw [hUframe j hj0 hj1]
        simp [T, Function.update_of_ne hj0,
          Function.update_of_ne hj1]

end ShiTMReplayMarkSplit
