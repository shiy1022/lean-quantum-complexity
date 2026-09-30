import «AMPUNI-replay-table-clear»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayTableClear

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- One table or mirror stack is drained in exactly its length plus one
transition. Other stacks are framed. -/
theorem clear_one_run (p : Phase) (hp : p ≠ .done)
    (s : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (htarget : S (stack p) = s) :
    ∃ U : ∀ k, List (TopGam k),
      run^[s.length + 1]
        (some { l := some p, var := v, stk := S }) =
          some { l := some (next p), var := none, stk := U }
      ∧ U (stack p) = []
      ∧ ∀ j : TopK, j ≠ stack p → U j = S j := by
  induction s generalizing v S with
  | nil =>
      let U := Function.update S (stack p) []
      refine ⟨U, ?_, ?_, ?_⟩
      · simpa [U] using empty_step p hp v S htarget
      · simp [U]
      · intro j hj
        exact Function.update_of_ne hj _ _
  | cons c tail ih =>
      let T := Function.update S (stack p) tail
      have hTtarget : T (stack p) = tail := by simp [T]
      obtain ⟨U, hrun, hUtarget, hUframe⟩ :=
        ih (some c) T hTtarget
      refine ⟨U, ?_, hUtarget, ?_⟩
      · have hfirst : run^[1]
            (some { l := some p, var := v, stk := S }) =
              some { l := some p, var := some c, stk := T } := by
          simpa [T] using cell_step p hp c tail v S htarget
        rw [show (c :: tail).length + 1 = 1 + (tail.length + 1) by
          simp only [List.length_cons]
          omega]
        exact iterTwo run 1 (tail.length + 1) _ _ _ hfirst hrun
      · intro j hj
        rw [hUframe j hj]
        exact Function.update_of_ne hj _ _

end ShiTMReplayTableClear
