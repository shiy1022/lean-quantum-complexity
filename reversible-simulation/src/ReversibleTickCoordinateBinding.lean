import ReversibleSymbolicCellBindingClock
import ReversibleNaturalTickCompilation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin

structure CoordinateBindingRegisters (R : Type) where
  input : R
  capacity : R
  position : R
  query : R
  target : R
  tmp : R

structure CoordinateBindingRegisters.Valid {R : Type} (r : CoordinateBindingRegisters R) : Prop where
  input_target : r.input ≠ r.target
  input_query : r.input ≠ r.query
  input_tmp : r.input ≠ r.tmp
  capacity_target : r.capacity ≠ r.target
  capacity_query : r.capacity ≠ r.query
  capacity_tmp : r.capacity ≠ r.tmp
  position_target : r.position ≠ r.target
  position_query : r.position ≠ r.query
  position_tmp : r.position ≠ r.tmp
  query_target : r.query ≠ r.target
  query_tmp : r.query ≠ r.tmp
  target_tmp : r.target ≠ r.tmp

variable {R L : Type} [DecidableEq R]

noncomputable def tickCoordinateOffset (tm : Turing.FinTM2) : TickSymbolicCoordinate tm → Nat
  | .inl (.inl l) => ((Fintype.equivFin (Option tm.Λ)) l).val
  | .inl (.inr v) => Fintype.card (Option tm.Λ) + ((Fintype.equivFin tm.σ) v).val
  | .inr (_, a) => Fintype.card (Option tm.Λ) + Fintype.card tm.σ +
      ((Fintype.equivFin (Option (MachineSymbol tm))) a).val

noncomputable def TickCoordinateBindingLabels (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R)
    (coordinate : TickSymbolicCoordinate tm) (L : Type) : Type :=
  match coordinate with
  | .inl z => AddressBindingLabels (tickCoordinateOffset tm (.inl z)) 1 0 L
  | .inr ((k, p), a) => SymbolicCellBindingLabels p r.input r.capacity r.query r.target
      (tickCoordinateOffset tm (.inr ((k, p), a))) ((Fintype.equivFin tm.K) k).val
      (Fintype.card (Option (MachineSymbol tm))) L

noncomputable def tickCoordinateBindingEntry (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R)
    (coordinate : TickSymbolicCoordinate tm) (L : Type) : TickCoordinateBindingLabels tm r coordinate L :=
  match coordinate with
  | .inl z => .inl 0
  | .inr _ => .inl 0

noncomputable def tickCoordinateBindingExit (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R)
    (coordinate : TickSymbolicCoordinate tm) (l : L) : TickCoordinateBindingLabels tm r coordinate L :=
  match coordinate with
  | .inl z => .inr (.inr (.inr (.inr l)))
  | .inr ((k, p), a) => symbolicCellBindingExit p r.input r.capacity r.query r.target
      (tickCoordinateOffset tm (.inr ((k, p), a))) ((Fintype.equivFin tm.K) k).val
      (Fintype.card (Option (MachineSymbol tm))) l

noncomputable def tickCoordinateBindingCode (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R)
    (coordinate : TickSymbolicCoordinate tm) (caller : L → CounterInstr R L) (stop : L) :
    TickCoordinateBindingLabels tm r coordinate L → CounterInstr R (TickCoordinateBindingLabels tm r coordinate L) :=
  match coordinate with
  | .inl z => addressBindingCode caller r.input r.target r.tmp (tickCoordinateOffset tm (.inl z)) 1 0 stop
  | .inr ((k, p), a) => symbolicCellBindingCode p caller r.input r.capacity r.position r.query r.target r.tmp
      (tickCoordinateOffset tm (.inr ((k, p), a))) ((Fintype.equivFin tm.K) k).val
      (Fintype.card (Option (MachineSymbol tm))) stop

noncomputable def tickCoordinateBindingSteps (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R)
    (coordinate : TickSymbolicCoordinate tm) (cs : R → Nat) : Nat :=
  match coordinate with
  | .inl z => (2 * cs r.target + 1) + ((7 * cs r.input + 2) + tickCoordinateOffset tm (.inl z))
  | .inr ((k, p), a) => symbolicCellBindingSteps p r.input r.capacity r.position r.query r.target
      (tickCoordinateOffset tm (.inr ((k, p), a))) ((Fintype.equivFin tm.K) k).val
      (Fintype.card (Option (MachineSymbol tm))) cs

noncomputable def tickCoordinateAddress (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R)
    (coordinate : TickSymbolicCoordinate tm) (cs : R → Nat) : Nat :=
  cs r.input + naturalConfigurationAddress tm (cs r.capacity)
    (tickSymbolicCoordinateEval (cs r.capacity) (cs r.position) coordinate)

noncomputable instance tickCoordinateBindingFintype (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R)
    (coordinate : TickSymbolicCoordinate tm) [Fintype L] : Fintype (TickCoordinateBindingLabels tm r coordinate L) := by
  cases coordinate with
  | inl z => exact inferInstanceAs (Fintype (AddressBindingLabels (tickCoordinateOffset tm (.inl z)) 1 0 L))
  | inr z =>
    exact inferInstanceAs (Fintype (SymbolicCellBindingLabels z.1.2 r.input r.capacity r.query r.target
      (tickCoordinateOffset tm (.inr z)) ((Fintype.equivFin tm.K) z.1.1).val
      (Fintype.card (Option (MachineSymbol tm))) L))

end ShiReversibleGenerator
