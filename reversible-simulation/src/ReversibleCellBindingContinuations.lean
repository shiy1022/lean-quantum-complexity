import ReversibleTickCoordinateBindingClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
variable {R L : Type} [DecidableEq R]

theorem cellAddressBindingCode_embed (caller : L → CounterInstr R L) (input capacity index target tmp : R)
    (offset rank stride : Nat) (stop l : L) :
    cellAddressBindingCode caller input capacity index target tmp offset rank stride stop
      (cellAddressBindingExit input capacity index target offset rank stride l) =
    (caller l).relabel (cellAddressBindingExit input capacity index target offset rank stride) := by
  let atoms := cellAddressAtoms input capacity index target offset rank stride
  change (arithmeticCode atoms (clearCode index caller stop) tmp (.inl 0)
    (arithmeticExit atoms (.inr l))).relabel Sum.inr = _
  rw [arithmeticCode_embed_fixed]
  change (((caller l).relabel Sum.inr).relabel (arithmeticExit atoms)).relabel Sum.inr = _
  cases caller l <;> rfl

theorem symbolicCellBindingCode_embed (p : TickIndexExpr) (caller : L → CounterInstr R L)
    (input capacity position index target tmp : R) (offset rank stride : Nat) (stop l : L) :
    symbolicCellBindingCode p caller input capacity position index target tmp offset rank stride stop
      (symbolicCellBindingExit p input capacity index target offset rank stride l) =
    (caller l).relabel (symbolicCellBindingExit p input capacity index target offset rank stride) := by
  rw [symbolicCellBindingCode, symbolicCellBindingExit, indexExpressionCode_embed, cellAddressBindingCode_embed]
  cases caller l <;> rfl

theorem tickCoordinateBindingCode_embed (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R)
    (coordinate : TickSymbolicCoordinate tm) (caller : L → CounterInstr R L) (stop l : L) :
    tickCoordinateBindingCode tm r coordinate caller stop (tickCoordinateBindingExit tm r coordinate l) =
      (caller l).relabel (tickCoordinateBindingExit tm r coordinate) := by
  cases coordinate with
  | inl z => exact addressBindingCode_embed _ _ _ _ _ _ _ _ _
  | inr z => exact symbolicCellBindingCode_embed _ _ _ _ _ _ _ _ _ _ _ _ _

end ShiReversibleGenerator
