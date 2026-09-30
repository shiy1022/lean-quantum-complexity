import «AMPUNI-replay-reload»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayReload

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

/-- Transfer all saved cells to the input while copying them to scratch.
Both stacks acquire the reverse of the archived list, so for the archived
reverse of the original input they recover the original input. -/
theorem transfer_all_run (s : List Cell) (v : Sig)
    (S : ∀ k, List (TopGam k)) (harchive : S archive = s) :
    ∃ U : ∀ k, List (TopGam k),
      run^[s.length + 1]
        (some { l := some (0 : ReloadLabel), var := v, stk := S }) =
          some { l := some (1 : ReloadLabel), var := none, stk := U }
      ∧ U archive = []
      ∧ U source = s.reverse ++ S source
      ∧ U scratch = s.reverse ++ S scratch
      ∧ ∀ j : TopK, j ≠ source → j ≠ scratch → j ≠ archive → U j = S j := by
  induction s generalizing v S with
  | nil =>
      let U := Function.update S archive []
      refine ⟨U, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [U] using transfer_empty_step v S harchive
      · simp [U]
      · change (Function.update S archive []) source = [] ++ S source
        rw [Function.update_of_ne (by decide)]
        rfl
      · change (Function.update S archive []) scratch = [] ++ S scratch
        rw [Function.update_of_ne (by decide)]
        rfl
      · intro j _ _ hj
        exact Function.update_of_ne hj _ _
  | cons c tail ih =>
      let T : ∀ k : TopK, List (TopGam k) :=
        Function.update
          (Function.update (Function.update S archive tail) source
            (c :: S source)) scratch (c :: S scratch)
      have hTarchive : T archive = tail := by
        change (Function.update
          (Function.update (Function.update S archive tail) source
            (c :: S source)) scratch (c :: S scratch)) archive = tail
        rw [Function.update_of_ne (by decide),
          Function.update_of_ne (by decide), Function.update_self]
      have hTsource : T source = c :: S source := by
        change (Function.update
          (Function.update (Function.update S archive tail) source
            (c :: S source)) scratch (c :: S scratch)) source = c :: S source
        rw [Function.update_of_ne (by decide), Function.update_self]
      have hTscratch : T scratch = c :: S scratch := by
        change (Function.update
          (Function.update (Function.update S archive tail) source
            (c :: S source)) scratch (c :: S scratch)) scratch = c :: S scratch
        rw [Function.update_self]
      have hTframe (j : TopK) (hj0 : j ≠ source) (hj1 : j ≠ scratch)
          (hj2 : j ≠ archive) : T j = S j := by
        change (Function.update
          (Function.update (Function.update S archive tail) source
            (c :: S source)) scratch (c :: S scratch)) j = S j
        rw [Function.update_of_ne hj1, Function.update_of_ne hj0,
          Function.update_of_ne hj2]
      obtain ⟨U, hrun, hUarchive, hUsource, hUscratch, hUframe⟩ :=
        ih (some c) T hTarchive
      refine ⟨U, ?_, hUarchive, ?_, ?_, ?_⟩
      · have hfirst : run^[1]
            (some { l := some (0 : ReloadLabel), var := v, stk := S }) =
              some { l := some (0 : ReloadLabel), var := some c, stk := T } := by
          simpa [T] using transfer_cell_step c tail v S harchive
        rw [show (c :: tail).length + 1 = 1 + (tail.length + 1) by
          simp only [List.length_cons]
          omega]
        exact iterTwo run 1 (tail.length + 1) _ _ _ hfirst hrun
      · rw [hUsource, hTsource]
        simp [List.reverse_cons, List.append_assoc]
      · rw [hUscratch, hTscratch]
        simp [List.reverse_cons, List.append_assoc]
      · intro j hj0 hj1 hj2
        rw [hUframe j hj0 hj1 hj2, hTframe j hj0 hj1 hj2]

end ShiTMReplayReload
