import ReversibleFormulaPrinterRun

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula
variable {R : Type} [DecidableEq R]

def fixedNodeLayerCount (ts : List (FixedNodeTemplate R)) : Nat :=
  (ts.map (fun t => t.kind.layers)).sum

theorem FixedNodeTemplate.counters_count (t : FixedNodeTemplate R) (r : NodePrinterRegisters R)
    (hp : r.count ≠ r.p) (hq : r.count ≠ r.q) (hr : r.count ≠ r.r) (cs : R → Nat) :
    t.counters r cs r.count = cs r.count + t.kind.layers := by
  simp [counters, fields, nodeFieldResult_other, hp, hq, hr]

theorem fixedNodeCounters_count (r : NodePrinterRegisters R) (ts : List (FixedNodeTemplate R))
    (hp : r.count ≠ r.p) (hq : r.count ≠ r.q) (hr : r.count ≠ r.r) (cs : R → Nat) :
    fixedNodeCounters r ts cs r.count = cs r.count + fixedNodeLayerCount ts := by
  induction ts generalizing cs with
  | nil => simp [fixedNodeCounters, fixedNodeLayerCount]
  | cons t ts ih =>
      simp [fixedNodeCounters, ih, t.counters_count r hp hq hr, fixedNodeLayerCount, Nat.add_assoc]

def formulaElementaryLayers {ι : Type} : Formula ι → Nat
  | .constant b => if b then 1 else 0
  | .input _ => 1
  | .neg p => formulaElementaryLayers p + 2
  | .conj p q => formulaElementaryLayers p + formulaElementaryLayers q + 37

theorem symbolicFormulaCompile_layers {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) :
    fixedNodeLayerCount ((symbolicFormulaCompile inputs base offset p).map
      (symbolicAssignmentTemplate backward)) = formulaElementaryLayers p := by
  induction p generalizing offset with
  | constant b => cases b <;> rfl
  | input i => rfl
  | neg p ih =>
      cases backward <;> simpa [fixedNodeLayerCount, symbolicFormulaCompile,
        symbolicAssignmentTemplate, AssignmentEmissionKind.layers, formulaElementaryLayers]
        using ih offset
  | conj p q ihp ihq =>
      have h₁ := ihp offset
      have h₂ := ihq (offset + p.size)
      simp [fixedNodeLayerCount, symbolicFormulaCompile, symbolicAssignmentTemplate,
        AssignmentEmissionKind.layers, formulaElementaryLayers] at h₁ h₂ ⊢
      omega

theorem formulaPrinter_layer_count {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) :
    fixedNodeLayerCount (formulaPrinterTemplates backward p inputs base offset) =
      formulaElementaryLayers p := by
  cases backward <;> simpa [formulaPrinterTemplates, fixedNodeLayerCount, List.map_reverse]
    using symbolicFormulaCompile_layers (R := R) _ p inputs base offset

theorem formulaPrinter_counter_count {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (r : NodePrinterRegisters R)
    (hp : r.count ≠ r.p) (hq : r.count ≠ r.q) (hr : r.count ≠ r.r) (cs : R → Nat) :
    fixedNodeCounters r (formulaPrinterTemplates backward p inputs base offset) cs r.count =
      cs r.count + formulaElementaryLayers p := by
  rw [fixedNodeCounters_count r _ hp hq hr, formulaPrinter_layer_count]

theorem formulaElementaryLayers_bound {ι : Type} (p : Formula ι) :
    formulaElementaryLayers p ≤ 37 * p.size := by
  induction p with
  | constant b => cases b <;> simp [formulaElementaryLayers, Formula.size]
  | input i => simp [formulaElementaryLayers, Formula.size]
  | neg p ih => simp only [formulaElementaryLayers, Formula.size]; omega
  | conj p q ihp ihq => simp only [formulaElementaryLayers, Formula.size]; omega

end ShiReversibleGenerator
