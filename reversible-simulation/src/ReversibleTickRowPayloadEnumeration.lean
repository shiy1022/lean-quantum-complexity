import ReversibleTickForestSymbolicPayload
import ReversibleTickCoordinateBoundedPayload
import ReversibleConfigurationEnumeration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem tickSymbolRowDescendingBytes_ofFn (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (input capacity outputBase count : Nat) :
    tickSymbolRowDescendingBytes tm stack inputStride bound backward input capacity outputBase count =
      (List.ofFn (fun i : Fin count => tickSymbolRowPayload tm stack inputStride bound backward input capacity outputBase i.val)).flatten := by
  induction count with
  | zero => simp [tickSymbolRowDescendingBytes]
  | succ k ih =>
    rw [tickSymbolRowDescendingBytes,ih,List.ofFn_succ']
    simp

theorem tickSymbolRowAscendingBytes_ofFn (tm : Turing.FinTM2) (stack : tm.K)
    (inputStride bound : Nat) (backward : Bool) (input capacity outputBase position count : Nat) :
    tickSymbolRowAscendingBytes tm stack inputStride bound backward input capacity outputBase position count =
      (List.ofFn (fun i : Fin count => tickSymbolRowPayload tm stack inputStride bound backward input capacity outputBase (position+i.val))).reverse.flatten := by
  induction count generalizing position with
  | zero => simp [tickSymbolRowAscendingBytes]
  | succ k ih =>
    rw [tickSymbolRowAscendingBytes,ih,List.ofFn_succ]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end ShiReversibleGenerator
