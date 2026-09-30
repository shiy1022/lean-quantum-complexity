import «AMPUNI-replay-table-clear-one-run»

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Turing Turing.TM2

namespace ShiTMReplayTableClear

open ShiTMLayoutMachine ShiTMRetainedTop

private theorem iterTwo {A : Type} (f : A → A) (a b : Nat)
    (x y z : A) (hxy : f^[a] x = y) (hyz : f^[b] y = z) :
    f^[a + b] x = z := by
  rw [show a + b = b + a by omega, Function.iterate_add_apply, hxy, hyz]

def clearCost (S : ∀ k, List (TopGam k)) : Nat :=
  (((S (stack .width)).length + 1) +
    ((S (stack .base)).length + 1)) +
    ((S (stack .widthMirror)).length + 1) +
    ((S (stack .baseMirror)).length + 1)

/-- Drain the old width/base tables and both mirrors. Every other stack,
including the retained headers and the saved input, is unchanged. -/
theorem clear_all_run (v : Sig) (S : ∀ k, List (TopGam k)) :
    ∃ U : ∀ k, List (TopGam k),
      run^[clearCost S]
        (some { l := some Phase.width, var := v, stk := S }) =
          some { l := some Phase.done, var := none, stk := U }
      ∧ U (stack .width) = []
      ∧ U (stack .base) = []
      ∧ U (stack .widthMirror) = []
      ∧ U (stack .baseMirror) = []
      ∧ ∀ j : TopK,
          j ≠ stack .width → j ≠ stack .base →
          j ≠ stack .widthMirror → j ≠ stack .baseMirror →
          U j = S j := by
  obtain ⟨A, hA, hAwidth, hAframe⟩ :=
    clear_one_run .width (by decide) (S (stack .width)) v S rfl
  have hAbase : A (stack .base) = S (stack .base) :=
    hAframe _ (by decide)
  obtain ⟨B, hB, hBbase, hBframe⟩ :=
    clear_one_run .base (by decide) (S (stack .base)) none A hAbase
  have hBwm : B (stack .widthMirror) =
      S (stack .widthMirror) := by
    rw [hBframe _ (by decide), hAframe _ (by decide)]
  obtain ⟨C, hC, hCwm, hCframe⟩ :=
    clear_one_run .widthMirror (by decide)
      (S (stack .widthMirror)) none B hBwm
  have hCbm : C (stack .baseMirror) =
      S (stack .baseMirror) := by
    rw [hCframe _ (by decide), hBframe _ (by decide),
      hAframe _ (by decide)]
  obtain ⟨U, hU, hUbm, hUframe⟩ :=
    clear_one_run .baseMirror (by decide)
      (S (stack .baseMirror)) none C hCbm
  refine ⟨U, ?_, ?_, ?_, ?_, hUbm, ?_⟩
  · have hAB := iterTwo run
      ((S (stack .width)).length + 1)
      ((S (stack .base)).length + 1) _ _ _ hA hB
    have hABC := iterTwo run
      (((S (stack .width)).length + 1) +
        ((S (stack .base)).length + 1))
      ((S (stack .widthMirror)).length + 1) _ _ _ hAB hC
    exact iterTwo run
      ((((S (stack .width)).length + 1) +
        ((S (stack .base)).length + 1)) +
        ((S (stack .widthMirror)).length + 1))
      ((S (stack .baseMirror)).length + 1) _ _ _ hABC hU
  · rw [hUframe _ (by decide), hCframe _ (by decide),
      hBframe _ (by decide)]
    exact hAwidth
  · rw [hUframe _ (by decide), hCframe _ (by decide)]
    exact hBbase
  · rw [hUframe _ (by decide)]
    exact hCwm
  · intro j hjw hjb hjwm hjbm
    rw [hUframe j hjbm, hCframe j hjwm,
      hBframe j hjb, hAframe j hjw]

end ShiTMReplayTableClear
