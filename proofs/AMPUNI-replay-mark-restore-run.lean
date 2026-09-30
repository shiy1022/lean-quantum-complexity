import «AMPUNI-replay-mark-restore»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayMarkRestore

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

/-- The mark restorer empties parser scratch stack 0 and puts the same unary
output count back above the archived input. -/
theorem restore_all_run (count : Nat) (v : Sig)
    (S : ∀ k, List (TopGam k))
    (hmarks : S marks = List.replicate count Cell.mark) :
    ∃ U : ∀ k, List (TopGam k),
      run^[count + 1]
        (some { l := some false, var := v, stk := S }) =
          some { l := some true, var := none, stk := U }
      ∧ U marks = []
      ∧ U archive = List.replicate count Cell.mark ++ S archive
      ∧ ∀ j : TopK, j ≠ archive → j ≠ marks → U j = S j := by
  induction count generalizing v S with
  | zero =>
      let U := Function.update S marks []
      refine ⟨U, ?_, ?_, ?_, ?_⟩
      · simpa [U] using empty_step v S (by simpa using hmarks)
      · simp [U]
      · change (Function.update S marks []) archive = [] ++ S archive
        rw [Function.update_of_ne (by decide)]
        rfl
      · intro j _ hj
        exact Function.update_of_ne hj _ _
  | succ count ih =>
      let T : ∀ k : TopK, List (TopGam k) :=
        Function.update
          (Function.update S marks (List.replicate count Cell.mark))
          archive (Cell.mark :: S archive)
      have hhead : S marks = Cell.mark :: List.replicate count Cell.mark := by
        simpa [List.replicate_succ] using hmarks
      have hTmarks : T marks = List.replicate count Cell.mark := by
        change (Function.update
          (Function.update S marks (List.replicate count Cell.mark))
          archive (Cell.mark :: S archive)) marks =
            List.replicate count Cell.mark
        rw [Function.update_of_ne (by decide), Function.update_self]
      have hTarchive : T archive = Cell.mark :: S archive := by
        change (Function.update
          (Function.update S marks (List.replicate count Cell.mark))
          archive (Cell.mark :: S archive)) archive = Cell.mark :: S archive
        rw [Function.update_self]
      have hTframe (j : TopK) (hj0 : j ≠ archive) (hj1 : j ≠ marks) :
          T j = S j := by
        change (Function.update
          (Function.update S marks (List.replicate count Cell.mark))
          archive (Cell.mark :: S archive)) j = S j
        rw [Function.update_of_ne hj0, Function.update_of_ne hj1]
      obtain ⟨U, hrun, hUmarks, hUarchive, hUframe⟩ :=
        ih (some Cell.mark) T hTmarks
      refine ⟨U, ?_, hUmarks, ?_, ?_⟩
      · have hfirst : run^[1]
            (some { l := some false, var := v, stk := S }) =
              some { l := some false, var := some Cell.mark, stk := T } := by
          simpa [T] using mark_step (List.replicate count Cell.mark) v S hhead
        rw [show count.succ + 1 = 1 + (count + 1) by omega]
        exact iterTwo run 1 (count + 1) _ _ _ hfirst hrun
      · rw [hUarchive, hTarchive]
        simpa [List.replicate_succ] using marks_commute count (S archive)
      · intro j hj0 hj1
        rw [hUframe j hj0 hj1, hTframe j hj0 hj1]

end ShiTMReplayMarkRestore
