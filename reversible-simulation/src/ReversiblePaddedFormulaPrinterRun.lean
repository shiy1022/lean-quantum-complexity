import ReversiblePaddedFormulaPayload

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula
variable {R L : Type} [DecidableEq R]

theorem falsePadding_reverse_payload (backward : Bool) (base count : Nat) :
    ((falsePadding base count).reverse.map (rawAssignmentPayload backward)).flatten = [] := by
  simp [falsePadding, List.map_reverse, List.map_map, Function.comp_def, rawAssignmentPayload,
    assignmentPayload, assignmentAtoms, emissionBytes]

theorem paddedFormulaSymbolicNodes_reverse_payload {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset bound : Nat) (result : SymbolicWire R)
    (cs : R → Nat) (hr : result.eval cs = cs base + offset + bound) :
    ((paddedFormulaSymbolicNodes p inputs base offset result).reverse.map
      (fun a => rawAssignmentPayload backward (a.eval cs))).flatten =
    ((p.paddedCompile (fun i => (inputs i).eval cs) (cs base + offset) bound).reverse.map
      (rawAssignmentPayload backward)).flatten := by
  have hp := p.size_pos
  simp only [paddedFormulaSymbolicNodes, Formula.paddedCompile, List.reverse_append,
    List.reverse_singleton, List.map_append, List.flatten_append, List.map_cons,
    List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    falsePadding_reverse_payload, List.nil_append]
  have hm := congrArg (fun xs => (xs.reverse.map (rawAssignmentPayload backward)).flatten)
    (symbolicFormulaCompile_eval p inputs base offset cs)
  simp only [List.map_reverse, List.map_map, Function.comp_def] at hm
  simp only [List.map_reverse]
  rw [hm]
  congr 1
  simp only [SymbolicAssignment.eval]
  rw [hr]
  simp only [SymbolicWire.eval, Formula.result]
  congr 2 <;> omega

theorem paddedFormulaPrinter_sources {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (result : SymbolicWire R)
    (r : NodePrinterRegisters R) (hb : r.SourceStable base)
    (hi : ∀ i, r.SourceStable (inputs i).source) (hz : r.SourceStable result.source) :
    ∀ t ∈ paddedFormulaPrinterTemplates backward p inputs base offset result,
      r.SourceStable t.x.source ∧ r.SourceStable t.y.source ∧ r.SourceStable t.z.source := by
  intro t ht
  have hm : t ∈ (paddedFormulaSymbolicNodes p inputs base offset result).map
      (symbolicAssignmentTemplate backward) := by
    cases backward <;> simpa [paddedFormulaPrinterTemplates] using ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
  apply symbolicAssignmentTemplate_sources
  intro s hs
  simp only [paddedFormulaSymbolicNodes, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · rcases symbolicFormulaCompile_sources p inputs base offset a ha s hs with h | ⟨i, h⟩
    · simpa [h] using hb
    · simpa [h] using hi i
  · simp [SymbolicAssignment.sources] at hs
    rcases hs with h | h
    · simpa [h] using hb
    · simpa [h] using hz

theorem paddedFormulaPrinter_stable {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (result : SymbolicWire R)
    (r : NodePrinterRegisters R) (hb : r.SourceStable base)
    (hi : ∀ i, r.SourceStable (inputs i).source) (hz : r.SourceStable result.source) :
    ∀ t ∈ paddedFormulaPrinterTemplates backward p inputs base offset result, t.StableSources r := by
  intro t ht
  obtain ⟨hx, hy, hz⟩ := paddedFormulaPrinter_sources backward p inputs base offset result r hb hi hz t ht
  exact ⟨⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩,
    ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1⟩, ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1⟩⟩

theorem paddedFormulaPrinter_operations_valid {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (result : SymbolicWire R)
    (r : NodePrinterRegisters R) (hr : r.Valid) (hb : r.SourceStable base)
    (hi : ∀ i, r.SourceStable (inputs i).source) (hz : r.SourceStable result.source) :
    ∀ t ∈ paddedFormulaPrinterTemplates backward p inputs base offset result,
      ∀ op ∈ t.ops r, op.Valid r.buf r.tmp := by
  intro t ht
  obtain ⟨hx, hy, hz⟩ := paddedFormulaPrinter_sources backward p inputs base offset result r hb hi hz t ht
  simp_all [FixedNodeTemplate.ops, nodeFieldOperations, GeneratorOperation.Valid, AffineAtom.Valid,
    NodePrinterRegisters.Valid, NodePrinterRegisters.SourceStable]

def paddedFormulaPrinterPayload {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset bound : Nat) (cs : R → Nat) :=
  let nodes := p.paddedCompile (fun i => (inputs i).eval cs) (cs base + offset) bound
  ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten

theorem paddedFormulaPrinter_bytes {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset bound : Nat) (result : SymbolicWire R)
    (r : NodePrinterRegisters R) (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hs : ∀ t ∈ paddedFormulaPrinterTemplates backward p inputs base offset result, t.StableSources r)
    (cs : R → Nat) (hz : result.eval cs = cs base + offset + bound) :
    fixedNodeBytes r (paddedFormulaPrinterTemplates backward p inputs base offset result) cs =
      paddedFormulaPrinterPayload backward p inputs base offset bound cs := by
  rw [fixedNodeBytes_payloads r _ hpq hpr hqr hs]
  cases backward <;> simp only [paddedFormulaPrinterTemplates, Bool.false_eq_true, Bool.true_eq,
    if_false, if_true, List.reverse_reverse, List.map_reverse, List.map_map, Function.comp_def,
    symbolicAssignmentTemplate_payload, paddedFormulaPrinterPayload]
  · exact paddedFormulaSymbolicNodes_payload false p inputs base offset bound result cs hz
  · simpa only [List.map_reverse] using
      paddedFormulaSymbolicNodes_reverse_payload true p inputs base offset bound result cs hz

/-- Runtime stride affects addresses, while the printer's entire control graph remains fixed. -/
theorem paddedFormulaPrinter_run {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset bound : Nat) (result : SymbolicWire R)
    (r : NodePrinterRegisters R) (caller : L → CounterInstr R L) (stop : L) (hr : r.Valid)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hbase : r.SourceStable base) (hi : ∀ i, r.SourceStable (inputs i).source)
    (hresult : r.SourceStable result.source) (cs : R → Nat)
    (hz : result.eval cs = cs base + offset + bound) (hb : cs r.buf = 0) (ht : cs r.tmp = 0)
    (ys : List Bool) :
    let ts := paddedFormulaPrinterTemplates backward p inputs base offset result
    CounterRun (fixedNodeCode r ts caller stop) ⟨some (fixedNodeEntry r ts stop), cs, ys⟩
      (fixedNodeSteps r ts cs) ⟨some (fixedNodeExit r ts stop), fixedNodeCounters r ts cs,
        paddedFormulaPrinterPayload backward p inputs base offset bound cs ++ ys⟩ := by
  have h := fixedNodeCode_run r (paddedFormulaPrinterTemplates backward p inputs base offset result)
    caller stop hr (paddedFormulaPrinter_operations_valid backward p inputs base offset result r hr hbase hi hresult)
    cs hb ht ys
  rw [paddedFormulaPrinter_bytes backward p inputs base offset bound result r hpq hpr hqr
    (paddedFormulaPrinter_stable backward p inputs base offset result r hbase hi hresult) cs hz] at h
  exact h

end ShiReversibleGenerator
