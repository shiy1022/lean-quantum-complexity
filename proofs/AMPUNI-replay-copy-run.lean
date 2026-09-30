import «AMPUNI-replay-preface»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayPreface

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- The archive phase traverses the entire input, putting its reverse on both
scratch and the retained archive. It stops at the *empty stack*, so the input
may contain any combination of marks and delimiters. -/
theorem copy_all_run (s : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (hsrc : S source = s) :
    ∃ U : ∀ k, List (TopGam k),
      run^[s.length + 1]
        (some { l := some copyLabel, var := v, stk := S }) =
          some { l := some restoreLabel, var := none, stk := U }
      ∧ U source = []
      ∧ U scratch = s.reverse ++ S scratch
      ∧ U archive = s.reverse ++ S archive
      ∧ ∀ j : TopK, j ≠ source → j ≠ scratch → j ≠ archive → U j = S j := by
  induction s generalizing v S with
  | nil =>
      let U := Function.update S source []
      refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [U] using copy_empty_step v S hsrc
      · change (Function.update S source []) source = []
        rw [Function.update_self]
      · change (Function.update S source []) scratch = [] ++ S scratch
        rw [Function.update_of_ne (by decide)]
        rfl
      · change (Function.update S source []) archive = [] ++ S archive
        rw [Function.update_of_ne (by decide)]
        rfl
      · intro j hj _ _
        exact Function.update_of_ne hj _ _
  | cons c tail ih =>
      let T : ∀ k : TopK, List (TopGam k) :=
        Function.update
          (Function.update (Function.update S source tail) scratch
            (c :: S scratch)) archive (c :: S archive)
      have hTsrc : T source = tail := by
        change (Function.update
          (Function.update (Function.update S source tail) scratch
            (c :: S scratch)) archive (c :: S archive)) source = tail
        rw [Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_self]
      have hTscratch : T scratch = c :: S scratch := by
        change (Function.update
          (Function.update (Function.update S source tail) scratch
            (c :: S scratch)) archive (c :: S archive)) scratch = c :: S scratch
        rw [Function.update_of_ne (by decide), Function.update_self]
      have hTarchive : T archive = c :: S archive := by
        change (Function.update
          (Function.update (Function.update S source tail) scratch
            (c :: S scratch)) archive (c :: S archive)) archive = c :: S archive
        rw [Function.update_self]
      have hTframe (j : TopK) (hj0 : j ≠ source) (hj1 : j ≠ scratch)
          (hj2 : j ≠ archive) : T j = S j := by
        change (Function.update
          (Function.update (Function.update S source tail) scratch
            (c :: S scratch)) archive (c :: S archive)) j = S j
        rw [Function.update_of_ne hj2, Function.update_of_ne hj1,
          Function.update_of_ne hj0]
      obtain ⟨U, hrun, hUsrc, hUscratch, hUarchive, hUframe⟩ :=
        ih (some c) T hTsrc
      refine ⟨U, ?_, hUsrc, ?_, ?_, ?_⟩
      · have hfirst : run^[1]
            (some { l := some copyLabel, var := v, stk := S }) =
              some { l := some copyLabel, var := some c, stk := T } := by
          simpa [T] using copy_cell_step c tail v S hsrc
        have h := iterTwo run 1 (tail.length + 1) _ _ _ hfirst hrun
        have hcost : (c :: tail).length + 1 = 1 + (tail.length + 1) := by
          simp only [List.length_cons]
          omega
        rw [hcost]
        exact h
      · rw [hUscratch, hTscratch]
        simp [List.reverse_cons, List.append_assoc]
      · rw [hUarchive, hTarchive]
        simp [List.reverse_cons, List.append_assoc]
      · intro j hj0 hj1 hj2
        rw [hUframe j hj0 hj1 hj2, hTframe j hj0 hj1 hj2]

end ShiTMReplayPreface
