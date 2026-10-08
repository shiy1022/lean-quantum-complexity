import ReversibleCoordinateBindingFrames
import ReversibleFormulaInputCompiler
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R : Type} [DecidableEq R]

/-- One actual address-binding task for each input occurrence of a fixed formula leaf. -/
noncomputable def leafInputBindingTasks (tm : Turing.FinTM2)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R) :
    List (CoordinateBindingTask tm R) :=
  List.ofFn (fun i => (p.inputList[i.val], slots i))

theorem leafInputBindingTasks_valid (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) :
    ∀ task ∈ leafInputBindingTasks tm p slots, (env.withTarget task.2).Valid := by
  simpa only [leafInputBindingTasks, List.forall_mem_ofFn_iff] using hv

theorem leafInputBindingTasks_distinct (tm : Turing.FinTM2)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hs : Function.Injective slots) :
    (leafInputBindingTasks tm p slots).Pairwise (fun a b => a.2 ≠ b.2) := by
  rw [leafInputBindingTasks, List.pairwise_ofFn]
  intro i j hij he
  exact (ne_of_lt hij) (hs he)

theorem leafInputBindingTasks_slot_values (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) (hs : Function.Injective slots)
    (cs : R → Nat) (i : Fin p.inputList.length) :
    coordinateBindingSequenceCounters tm env (leafInputBindingTasks tm p slots) cs (slots i) =
      tickCoordinateAddress tm (env.withTarget (slots i)) p.inputList[i.val] cs := by
  apply coordinateBindingSequence_slot_values tm env (leafInputBindingTasks tm p slots)
    (leafInputBindingTasks_valid tm env p slots hv) (leafInputBindingTasks_distinct tm p slots hs)
    cs (p.inputList[i.val], slots i)
  simp only [leafInputBindingTasks, List.mem_ofFn]
  exact ⟨i, rfl⟩

/-- The fixed interned printer reads the addresses established by the actual binding sequence. -/
theorem leafInputBindings_compile_eval (tm : Turing.FinTM2) (env : CoordinateBindingRegisters R)
    (p : Formula (TickSymbolicCoordinate tm)) (slots : Fin p.inputList.length → R)
    (hv : ∀ i, (env.withTarget (slots i)).Valid) (hs : Function.Injective slots)
    (cs : R → Nat) (base : R) (offset : Nat) :
    let after := coordinateBindingSequenceCounters tm env (leafInputBindingTasks tm p slots) cs
    (symbolicFormulaCompile (fun i => ⟨slots i, 0⟩) base offset p.intern).map
      (SymbolicAssignment.eval after) =
      p.rawCompile (fun coordinate => tickCoordinateAddress tm env coordinate cs) (after base + offset) := by
  dsimp only
  rw [symbolicFormulaCompile_eval]
  have hi : (fun i : Fin p.inputList.length =>
      (SymbolicWire.mk (slots i) 0).eval
        (coordinateBindingSequenceCounters tm env (leafInputBindingTasks tm p slots) cs)) =
      (fun i => tickCoordinateAddress tm env p.inputList[i.val] cs) := by
    funext i
    simp only [SymbolicWire.eval, Nat.add_zero]
    rw [leafInputBindingTasks_slot_values tm env p slots hv hs cs i]
    rfl
  rw [hi]
  exact Formula.intern_rawCompile p (fun coordinate => tickCoordinateAddress tm env coordinate cs) _

end ShiReversibleGenerator
