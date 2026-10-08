import ReversibleConstantFragment

set_option autoImplicit false
namespace ShiReversibleGenerator

inductive IndexUpdate where
  | add : Nat → IndexUpdate
  | sub : Nat → IndexUpdate

def IndexUpdate.amount : IndexUpdate → Nat
  | .add n | .sub n => n

def IndexUpdate.apply : IndexUpdate → Nat → Nat
  | .add n, v => v + n
  | .sub n, v => v - n

variable {R L : Type} [DecidableEq R]

def IndexUpdate.code (op : IndexUpdate) (caller : L → CounterInstr R L) (target : R) (stop : L) :
    ConstantLabel op.amount L → CounterInstr R (ConstantLabel op.amount L) :=
  match op with
  | .add n => incrementCode caller n target stop
  | .sub n => decrementCode caller n target stop

theorem IndexUpdate.code_embed (op : IndexUpdate) (caller : L → CounterInstr R L)
    (target : R) (stop l : L) : op.code caller target stop (.inr l) = (caller l).relabel Sum.inr := by
  cases op <;> rfl

theorem IndexUpdate.code_run (op : IndexUpdate) (caller : L → CounterInstr R L) (target : R) (stop : L)
    (cs : R → Nat) (ys : List Bool) :
    CounterRun (op.code caller target stop)
      ⟨some (constantFrom op.amount stop 0), cs, ys⟩ op.amount
      ⟨some (.inr stop), Function.update cs target (op.apply (cs target)), ys⟩ := by
  cases op with
  | add n =>
    simpa [IndexUpdate.code, IndexUpdate.amount, IndexUpdate.apply, withCounter] using
      increment_span caller n target stop ⟨none, cs, ys⟩ n 0 (cs target) (by omega)
  | sub n =>
    simpa [IndexUpdate.code, IndexUpdate.amount, IndexUpdate.apply, withCounter] using
      decrement_span caller n target stop ⟨none, cs, ys⟩ n 0 (cs target) (by omega)

end ShiReversibleGenerator
