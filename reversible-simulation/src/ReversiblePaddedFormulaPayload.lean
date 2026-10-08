import ReversibleFormulaLayerCount
import ReversiblePaddedFormula

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula
variable {R : Type} [DecidableEq R]

theorem falsePadding_payload (backward : Bool) (base count : Nat) :
    ((falsePadding base count).map (rawAssignmentPayload backward)).flatten = [] := by
  simp [falsePadding, List.map_map, Function.comp_def, rawAssignmentPayload,
    assignmentPayload, assignmentAtoms, emissionBytes]

def paddedFormulaSymbolicNodes {ι : Type} (p : Formula ι) (inputs : ι → SymbolicWire R)
    (base : R) (offset : Nat) (result : SymbolicWire R) : List (SymbolicAssignment R) :=
  symbolicFormulaCompile inputs base offset p ++ [.copy ⟨base, offset + (p.size - 1)⟩ result]

/-- Padding writes false to fresh zero targets and contributes no circuit layers. -/
theorem paddedFormulaSymbolicNodes_payload {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset bound : Nat) (result : SymbolicWire R)
    (cs : R → Nat) (hr : result.eval cs = cs base + offset + bound) :
    ((paddedFormulaSymbolicNodes p inputs base offset result).map
      (fun a => rawAssignmentPayload backward (a.eval cs))).flatten =
    ((p.paddedCompile (fun i => (inputs i).eval cs) (cs base + offset) bound).map
      (rawAssignmentPayload backward)).flatten := by
  have hp := p.size_pos
  simp only [paddedFormulaSymbolicNodes, Formula.paddedCompile, List.map_append,
    List.flatten_append, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, falsePadding_payload]
  have hm := congrArg (List.map (rawAssignmentPayload backward))
    (symbolicFormulaCompile_eval p inputs base offset cs)
  simp only [List.map_map, Function.comp_def] at hm
  rw [hm]
  congr 1
  simp only [SymbolicAssignment.eval]
  rw [hr]
  simp only [SymbolicWire.eval, Formula.result]
  congr 2 <;> omega

def paddedFormulaPrinterTemplates {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (result : SymbolicWire R) :=
  let nodes := (paddedFormulaSymbolicNodes p inputs base offset result).map
    (symbolicAssignmentTemplate backward)
  if backward then nodes else nodes.reverse

theorem paddedFormulaPrinter_layer_count {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (result : SymbolicWire R) :
    fixedNodeLayerCount (paddedFormulaPrinterTemplates backward p inputs base offset result) =
      formulaElementaryLayers p + 1 := by
  have h := symbolicFormulaCompile_layers backward p inputs base offset
  cases backward <;> simp [paddedFormulaPrinterTemplates, paddedFormulaSymbolicNodes,
    fixedNodeLayerCount, List.map_reverse, symbolicAssignmentTemplate, AssignmentEmissionKind.layers] at h ⊢ <;> omega

end ShiReversibleGenerator
