import ReversibleLeafInputBindings

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable {R L : Type} [DecidableEq R]

theorem coordinateBindingSequenceCode_embed (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (tasks : List (CoordinateBindingTask tm R)) (caller : L → CounterInstr R L) (stop l : L) :
    coordinateBindingSequenceCode tm env tasks caller stop (coordinateBindingSequenceExit tm env tasks l) =
      (caller l).relabel (coordinateBindingSequenceExit tm env tasks) := by
  induction tasks with
  | nil =>
    change caller l = (caller l).relabel (fun x => x)
    cases caller l <;> rfl
  | cons task tasks ih =>
    change tickCoordinateBindingCode tm (env.withTarget task.2) task.1
      (coordinateBindingSequenceCode tm env tasks caller stop) (coordinateBindingSequenceEntry tm env tasks stop)
      (tickCoordinateBindingExit tm (env.withTarget task.2) task.1
        (coordinateBindingSequenceExit tm env tasks l)) = _
    rw [tickCoordinateBindingCode_embed, ih]
    cases caller l <;> rfl

end ShiReversibleGenerator
