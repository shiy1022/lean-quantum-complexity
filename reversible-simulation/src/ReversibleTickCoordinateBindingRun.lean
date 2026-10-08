import ReversibleTickCoordinateBinding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
variable {R L : Type} [DecidableEq R]

/-- Every fixed symbolic coordinate is bound to its exact relocated input wire address. -/
theorem tickCoordinateBindingCode_run (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R)
    (coordinate : TickSymbolicCoordinate tm) (caller : L → CounterInstr R L) (stop : L)
    (hv : r.Valid) (cs : R → Nat) (hq : cs r.query = 0) (hx : cs r.tmp = 0) (ys : List Bool) :
    CounterRun (tickCoordinateBindingCode tm r coordinate caller stop)
      ⟨some (tickCoordinateBindingEntry tm r coordinate L), cs, ys⟩ (tickCoordinateBindingSteps tm r coordinate cs)
      ⟨some (tickCoordinateBindingExit tm r coordinate stop),
        Function.update cs r.target (tickCoordinateAddress tm r coordinate cs), ys⟩ := by
  cases coordinate with
  | inl z =>
    have h := addressBindingCode_run caller r.input r.target r.tmp (tickCoordinateOffset tm (.inl z)) 1 0 stop
      hv.input_target hv.input_tmp hv.target_tmp cs hx ys
    cases z with
    | inl l =>
      simpa [tickCoordinateBindingCode, tickCoordinateBindingEntry, tickCoordinateBindingExit,
        tickCoordinateBindingSteps, tickCoordinateAddress, tickCoordinateOffset,
        naturalConfigurationAddress, tickSymbolicCoordinateEval] using h
    | inr v =>
      simpa [tickCoordinateBindingCode, tickCoordinateBindingEntry, tickCoordinateBindingExit,
        tickCoordinateBindingSteps, tickCoordinateAddress, tickCoordinateOffset,
        naturalConfigurationAddress, tickSymbolicCoordinateEval] using h
  | inr z =>
    let coordinate : TickSymbolicCoordinate tm := .inr z
    have h := symbolicCellBindingCode_run z.1.2 caller r.input r.capacity r.position r.query r.target r.tmp
      (tickCoordinateOffset tm coordinate) ((Fintype.equivFin tm.K) z.1.1).val
      (Fintype.card (Option (MachineSymbol tm))) stop
      hv.capacity_query hv.position_query hv.input_query hv.capacity_tmp hv.position_tmp hv.input_tmp
      hv.query_target hv.query_tmp hv.input_target hv.capacity_target hv.target_tmp cs hq hx ys
    have he : symbolicCellAddress z.1.2 r.input r.capacity r.position
        (tickCoordinateOffset tm coordinate) ((Fintype.equivFin tm.K) z.1.1).val
        (Fintype.card (Option (MachineSymbol tm))) cs = tickCoordinateAddress tm r coordinate cs := by
      simp only [symbolicCellAddress, tickCoordinateAddress, coordinate, tickCoordinateOffset,
        naturalConfigurationAddress, tickSymbolicCoordinateEval]
      ring
    rw [he] at h
    simpa only [tickCoordinateBindingCode, tickCoordinateBindingEntry, tickCoordinateBindingExit,
      tickCoordinateBindingSteps, coordinate] using h

end ShiReversibleGenerator
