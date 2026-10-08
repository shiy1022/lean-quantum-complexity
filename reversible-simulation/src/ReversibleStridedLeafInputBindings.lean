import ReversibleStridedCoordinateBindingBudget
import ReversibleLeafInputBindings

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R : Type} [DecidableEq R]

theorem stridedLeafInputBindingTasks_slot_values (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) (hs : Function.Injective slots)
    (cs : R → Nat) (i : Fin p.inputList.length) :
    stridedCoordinateBindingSequenceCounters tm env inputStride (leafInputBindingTasks tm p slots) cs (slots i) =
      stridedTickCoordinateAddress tm (env.withTarget (slots i)) inputStride p.inputList[i.val] cs := by
  apply stridedCoordinateBindingSequence_slot_values tm env inputStride (leafInputBindingTasks tm p slots)
    (leafInputBindingTasks_valid tm env p slots hv) (leafInputBindingTasks_distinct tm p slots hs)
    cs (p.inputList[i.val], slots i)
  simp only [leafInputBindingTasks, List.mem_ofFn]
  exact ⟨i, rfl⟩

/-- The fixed interned printer reads the addresses established by the actual binding sequence. -/
theorem stridedLeafInputBindings_compile_eval (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R) (inputStride : Nat)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) (hs : Function.Injective slots)
    (cs : R → Nat) (base : R) (offset : Nat) :
    let after := stridedCoordinateBindingSequenceCounters tm env inputStride (leafInputBindingTasks tm p slots) cs
    (symbolicFormulaCompile (fun i => ⟨slots i, 0⟩) base offset p.intern).map
      (SymbolicAssignment.eval after) =
      p.rawCompile (fun coordinate => stridedTickCoordinateAddress tm env inputStride coordinate cs) (after base + offset) := by
  dsimp only
  rw [symbolicFormulaCompile_eval]
  have hi : (fun i : Fin p.inputList.length =>
      (SymbolicWire.mk (slots i) 0).eval
        (stridedCoordinateBindingSequenceCounters tm env inputStride (leafInputBindingTasks tm p slots) cs)) =
      (fun i => stridedTickCoordinateAddress tm env inputStride p.inputList[i.val] cs) := by
    funext i
    simp only [SymbolicWire.eval, Nat.add_zero]
    rw [stridedLeafInputBindingTasks_slot_values tm env inputStride p slots hv hs cs i]
    rfl
  rw [hi]
  exact Formula.intern_rawCompile p (fun coordinate => stridedTickCoordinateAddress tm env inputStride coordinate cs) _

end ShiReversibleGenerator
