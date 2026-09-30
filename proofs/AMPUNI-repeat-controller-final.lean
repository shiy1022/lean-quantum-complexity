import «AMPUNI-repeat-controller-step»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatController

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- Final cleanup empties the active unary header bank and preserves every
other stack, including the amplified output, in exactly `length + 1` steps. -/
theorem clear_header_run
    (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (b : Bool) (xs : List Bool)
    (S : ∀ j, List (Gam G j)) (v : Option Bool) (w : W)
    (hh : S (.inr (header b)) = xs) :
    (ShiTMSubroutine.run
      (machine M entry terminal input output decodeOutput encodeInput))^[
        xs.length + 1]
      (some ⟨some (phase b .clearHeader), (v, w), S⟩) =
        some ⟨none, (none, w),
          Function.update S (.inr (header b)) []⟩ := by
  induction xs generalizing S v with
  | nil =>
      simp [ShiTMSubroutine.run, machine, phase, step, stepAux, hh]
  | cons x xs ih =>
      let S₁ := Function.update S (.inr (header b)) xs
      have hh₁ : S₁ (.inr (header b)) = xs := by simp [S₁]
      have hstep : ShiTMSubroutine.run
          (machine M entry terminal input output decodeOutput encodeInput)
            (some ⟨some (phase b .clearHeader), (v, w), S⟩) =
          some ⟨some (phase b .clearHeader), (some x, w), S₁⟩ := by
        simp [ShiTMSubroutine.run, machine, phase, step, stepAux, hh, S₁]
      have h := ih S₁ (some x) hh₁
      rw [List.length_cons, Function.iterate_succ_apply, hstep, h]
      congr 1
      congr 1
      simp [S₁]

end ShiTMRepeatController
