import ReversibleTickCoordinateBindingRun
import ReversibleCellBindingContinuations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
variable {R L : Type} [DecidableEq R]

noncomputable def StridedTickCoordinateBindingLabels (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R) (inputStride : Nat)
    (coordinate : TickSymbolicCoordinate tm) (L : Type) : Type :=
  match coordinate with
  | .inl z => AddressBindingLabels (tickCoordinateOffset tm (.inl z) * inputStride) 1 0 L
  | .inr ((k, p), a) => SymbolicCellBindingLabels p r.input r.capacity r.query r.target
      (tickCoordinateOffset tm (.inr ((k, p), a)) * inputStride) ((Fintype.equivFin tm.K) k).val
      (Fintype.card (Option (MachineSymbol tm)) * inputStride) L

noncomputable def stridedTickCoordinateBindingEntry (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R) (inputStride : Nat)
    (coordinate : TickSymbolicCoordinate tm) (L : Type) : StridedTickCoordinateBindingLabels tm r inputStride coordinate L :=
  match coordinate with
  | .inl z => .inl 0
  | .inr _ => .inl 0

noncomputable def stridedTickCoordinateBindingExit (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R) (inputStride : Nat)
    (coordinate : TickSymbolicCoordinate tm) (l : L) : StridedTickCoordinateBindingLabels tm r inputStride coordinate L :=
  match coordinate with
  | .inl z => .inr (.inr (.inr (.inr l)))
  | .inr ((k, p), a) => symbolicCellBindingExit p r.input r.capacity r.query r.target
      (tickCoordinateOffset tm (.inr ((k, p), a)) * inputStride) ((Fintype.equivFin tm.K) k).val
      (Fintype.card (Option (MachineSymbol tm)) * inputStride) l

noncomputable def stridedTickCoordinateBindingCode (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R) (inputStride : Nat)
    (coordinate : TickSymbolicCoordinate tm) (caller : L → CounterInstr R L) (stop : L) :
    StridedTickCoordinateBindingLabels tm r inputStride coordinate L → CounterInstr R (StridedTickCoordinateBindingLabels tm r inputStride coordinate L) :=
  match coordinate with
  | .inl z => addressBindingCode caller r.input r.target r.tmp (tickCoordinateOffset tm (.inl z) * inputStride) 1 0 stop
  | .inr ((k, p), a) => symbolicCellBindingCode p caller r.input r.capacity r.position r.query r.target r.tmp
      (tickCoordinateOffset tm (.inr ((k, p), a)) * inputStride) ((Fintype.equivFin tm.K) k).val
      (Fintype.card (Option (MachineSymbol tm)) * inputStride) stop

noncomputable def stridedTickCoordinateBindingSteps (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R) (inputStride : Nat)
    (coordinate : TickSymbolicCoordinate tm) (cs : R → Nat) : Nat :=
  match coordinate with
  | .inl z => (2 * cs r.target + 1) + ((7 * cs r.input + 2) + tickCoordinateOffset tm (.inl z) * inputStride)
  | .inr ((k, p), a) => symbolicCellBindingSteps p r.input r.capacity r.position r.query r.target
      (tickCoordinateOffset tm (.inr ((k, p), a)) * inputStride) ((Fintype.equivFin tm.K) k).val
      (Fintype.card (Option (MachineSymbol tm)) * inputStride) cs

noncomputable def stridedTickCoordinateAddress (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R) (inputStride : Nat)
    (coordinate : TickSymbolicCoordinate tm) (cs : R → Nat) : Nat :=
  cs r.input + inputStride * naturalConfigurationAddress tm (cs r.capacity)
    (tickSymbolicCoordinateEval (cs r.capacity) (cs r.position) coordinate)

noncomputable instance stridedTickCoordinateBindingFintype (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R) (inputStride : Nat)
    (coordinate : TickSymbolicCoordinate tm) [Fintype L] : Fintype (StridedTickCoordinateBindingLabels tm r inputStride coordinate L) := by
  cases coordinate with
  | inl z => exact inferInstanceAs (Fintype (AddressBindingLabels (tickCoordinateOffset tm (.inl z) * inputStride) 1 0 L))
  | inr z =>
    exact inferInstanceAs (Fintype (SymbolicCellBindingLabels z.1.2 r.input r.capacity r.query r.target
      (tickCoordinateOffset tm (.inr z) * inputStride) ((Fintype.equivFin tm.K) z.1.1).val
      (Fintype.card (Option (MachineSymbol tm)) * inputStride) L))


end ShiReversibleGenerator
