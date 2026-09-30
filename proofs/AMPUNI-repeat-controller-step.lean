import «AMPUNI-repeat-controller»

set_option autoImplicit false
set_option maxHeartbeats 2000000

open Turing Turing.TM2
namespace ShiTMRepeatController

variable {K L W : Type} [DecidableEq K] [DecidableEq L]
    {G : K → Type}

/-- With another round counted, the active source terminal enters the
output-to-scratch transfer, consuming exactly one counter token. -/
theorem terminal_more (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (b : Bool) (S : ∀ j, List (Gam G j))
    (v : Option Bool) (w : W) (x : Bool) (xs : List Bool)
    (hc : S (.inr counter) = x :: xs) :
    ShiTMSubroutine.run
      (machine M entry terminal input output decodeOutput encodeInput)
        (some ⟨some (body b terminal), (v, w), S⟩) =
      some ⟨some (phase b .toScratch), (some x, w),
        Function.update S (.inr counter) xs⟩ := by
  simp [ShiTMSubroutine.run, machine, body, phase, step, stepAux, hc]

/-- When the counter is empty, the active source terminal enters final
header cleanup with the amplified output stack untouched. -/
theorem terminal_done (M : L → Stmt G L (Option Bool × W))
    (entry terminal : L) (input output : K)
    (decodeOutput : G output → Bool)
    (encodeInput : Bool → G input)
    (b : Bool) (S : ∀ j, List (Gam G j))
    (v : Option Bool) (w : W)
    (hc : S (.inr counter) = []) :
    ShiTMSubroutine.run
      (machine M entry terminal input output decodeOutput encodeInput)
        (some ⟨some (body b terminal), (v, w), S⟩) =
      some ⟨some (phase b .clearHeader), (none, w),
        Function.update S (.inr counter) []⟩ := by
  simp [ShiTMSubroutine.run, machine, body, phase, step, stepAux, hc]

end ShiTMRepeatController
