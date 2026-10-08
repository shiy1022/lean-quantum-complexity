import ReversibleStridedCoordinateBindingFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable {R L : Type} [DecidableEq R]

theorem stridedCoordinateBindingSequenceCode_embed (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (tasks : List (CoordinateBindingTask tm R)) (caller : L → CounterInstr R L) (stop l : L) :
    stridedCoordinateBindingSequenceCode tm env inputStride tasks caller stop (stridedCoordinateBindingSequenceExit tm env inputStride tasks l) =
      (caller l).relabel (stridedCoordinateBindingSequenceExit tm env inputStride tasks) := by
  induction tasks with
  | nil =>
    change caller l = (caller l).relabel (fun x => x)
    cases caller l <;> rfl
  | cons task tasks ih =>
    change stridedTickCoordinateBindingCode tm (env.withTarget task.2) inputStride task.1
      (stridedCoordinateBindingSequenceCode tm env inputStride tasks caller stop) (stridedCoordinateBindingSequenceEntry tm env inputStride tasks stop)
      (stridedTickCoordinateBindingExit tm (env.withTarget task.2) inputStride task.1
        (stridedCoordinateBindingSequenceExit tm env inputStride tasks l)) = _
    rw [stridedTickCoordinateBindingCode_embed, ih]
    cases caller l <;> rfl

end ShiReversibleGenerator
