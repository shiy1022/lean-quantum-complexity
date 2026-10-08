import ReversibleStridedTickCoordinateBinding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
local instance (tm : Turing.FinTM2) : Fintype tm.K := tm.kFin
local instance (tm : Turing.FinTM2) : Fintype tm.Λ := tm.ΛFin
local instance (tm : Turing.FinTM2) : Fintype tm.σ := tm.σFin
variable {R L : Type} [DecidableEq R]

/-- Every fixed symbolic coordinate is bound to its exact relocated input wire address. -/
theorem stridedTickCoordinateBindingCode_run (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R) (inputStride : Nat)
    (coordinate : TickSymbolicCoordinate tm) (caller : L → CounterInstr R L) (stop : L)
    (hv : r.Valid) (cs : R → Nat) (hq : cs r.query = 0) (hx : cs r.tmp = 0) (ys : List Bool) :
    CounterRun (stridedTickCoordinateBindingCode tm r inputStride coordinate caller stop)
      ⟨some (stridedTickCoordinateBindingEntry tm r inputStride coordinate L), cs, ys⟩ (stridedTickCoordinateBindingSteps tm r inputStride coordinate cs)
      ⟨some (stridedTickCoordinateBindingExit tm r inputStride coordinate stop),
        Function.update cs r.target (stridedTickCoordinateAddress tm r inputStride coordinate cs), ys⟩ := by
  cases coordinate with
  | inl z =>
    have h := addressBindingCode_run caller r.input r.target r.tmp (tickCoordinateOffset tm (.inl z) * inputStride) 1 0 stop
      hv.input_target hv.input_tmp hv.target_tmp cs hx ys
    cases z with
    | inl l =>
      simpa [stridedTickCoordinateBindingCode, stridedTickCoordinateBindingEntry, stridedTickCoordinateBindingExit,
        stridedTickCoordinateBindingSteps, stridedTickCoordinateAddress, tickCoordinateOffset,
        naturalConfigurationAddress, tickSymbolicCoordinateEval, Nat.mul_add, Nat.mul_comm] using h
    | inr v =>
      simpa [stridedTickCoordinateBindingCode, stridedTickCoordinateBindingEntry, stridedTickCoordinateBindingExit,
        stridedTickCoordinateBindingSteps, stridedTickCoordinateAddress, tickCoordinateOffset,
        naturalConfigurationAddress, tickSymbolicCoordinateEval, Nat.mul_add, Nat.mul_comm] using h
  | inr z =>
    let coordinate : TickSymbolicCoordinate tm := .inr z
    have h := symbolicCellBindingCode_run z.1.2 caller r.input r.capacity r.position r.query r.target r.tmp
      (tickCoordinateOffset tm coordinate * inputStride) ((Fintype.equivFin tm.K) z.1.1).val
      (Fintype.card (Option (MachineSymbol tm)) * inputStride) stop
      hv.capacity_query hv.position_query hv.input_query hv.capacity_tmp hv.position_tmp hv.input_tmp
      hv.query_target hv.query_tmp hv.input_target hv.capacity_target hv.target_tmp cs hq hx ys
    have he : symbolicCellAddress z.1.2 r.input r.capacity r.position
        (tickCoordinateOffset tm coordinate * inputStride) ((Fintype.equivFin tm.K) z.1.1).val
        (Fintype.card (Option (MachineSymbol tm)) * inputStride) cs = stridedTickCoordinateAddress tm r inputStride coordinate cs := by
      simp only [symbolicCellAddress, stridedTickCoordinateAddress, coordinate, tickCoordinateOffset,
        naturalConfigurationAddress, tickSymbolicCoordinateEval]
      ring
    rw [he] at h
    simpa only [stridedTickCoordinateBindingCode, stridedTickCoordinateBindingEntry, stridedTickCoordinateBindingExit,
      stridedTickCoordinateBindingSteps, coordinate] using h


theorem stridedTickCoordinateBindingCode_embed (tm : Turing.FinTM2) (r : CoordinateBindingRegisters R)
    (inputStride : Nat) (coordinate : TickSymbolicCoordinate tm) (caller : L → CounterInstr R L) (stop l : L) :
    stridedTickCoordinateBindingCode tm r inputStride coordinate caller stop
      (stridedTickCoordinateBindingExit tm r inputStride coordinate l) =
      (caller l).relabel (stridedTickCoordinateBindingExit tm r inputStride coordinate) := by
  cases coordinate with
  | inl z => exact addressBindingCode_embed _ _ _ _ _ _ _ _ _
  | inr z => exact symbolicCellBindingCode_embed _ _ _ _ _ _ _ _ _ _ _ _ _

end ShiReversibleGenerator
