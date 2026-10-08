import ReversibleFixedFormulaPrinter

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula
variable {R : Type} [DecidableEq R]

def SymbolicAssignment.sources : SymbolicAssignment R → List R
  | .constant t _ => [t.source]
  | .copy s t | .neg s t => [s.source, t.source]
  | .conj a b t => [a.source, b.source, t.source]

theorem symbolicFormulaCompile_sources {ι : Type} (p : Formula ι) (inputs : ι → SymbolicWire R)
    (base : R) (offset : Nat) (a : SymbolicAssignment R)
    (ha : a ∈ symbolicFormulaCompile inputs base offset p) (s : R) (hs : s ∈ a.sources) :
    s = base ∨ ∃ i, s = (inputs i).source := by
  induction p generalizing offset a with
  | constant b =>
      simp only [symbolicFormulaCompile, List.mem_singleton] at ha
      subst a
      exact Or.inl (by simpa [SymbolicAssignment.sources] using hs)
  | input i =>
      simp only [symbolicFormulaCompile, List.mem_singleton] at ha
      subst a
      simp [SymbolicAssignment.sources] at hs
      rcases hs with h | h
      · exact Or.inr ⟨i, h⟩
      · exact Or.inl h
  | neg p ih =>
      simp only [symbolicFormulaCompile, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact ih offset _ ha hs
      · exact Or.inl (by simpa [SymbolicAssignment.sources] using hs)
  | conj p q ihp ihq =>
      simp only [symbolicFormulaCompile, List.mem_append, List.mem_singleton] at ha
      rcases ha with (ha | ha) | rfl
      · exact ihp offset _ ha hs
      · exact ihq (offset + p.size) _ ha hs
      · exact Or.inl (by simpa [SymbolicAssignment.sources] using hs)

def NodePrinterRegisters.SourceStable (r : NodePrinterRegisters R) (s : R) : Prop :=
  s ≠ r.p ∧ s ≠ r.q ∧ s ≠ r.r ∧ s ≠ r.count ∧ s ≠ r.tmp

theorem symbolicAssignmentTemplate_sources (backward : Bool) (a : SymbolicAssignment R)
    (r : NodePrinterRegisters R) (hs : ∀ s ∈ a.sources, r.SourceStable s) :
    r.SourceStable (symbolicAssignmentTemplate backward a).x.source ∧
    r.SourceStable (symbolicAssignmentTemplate backward a).y.source ∧
    r.SourceStable (symbolicAssignmentTemplate backward a).z.source := by
  cases a <;> simp [SymbolicAssignment.sources] at hs <;>
    simpa [symbolicAssignmentTemplate] using hs

theorem formulaPrinter_sources {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (r : NodePrinterRegisters R)
    (hb : r.SourceStable base) (hi : ∀ i, r.SourceStable (inputs i).source) :
    ∀ t ∈ formulaPrinterTemplates backward p inputs base offset,
      r.SourceStable t.x.source ∧ r.SourceStable t.y.source ∧ r.SourceStable t.z.source := by
  intro t ht
  have hm : t ∈ (symbolicFormulaCompile inputs base offset p).map (symbolicAssignmentTemplate backward) := by
    cases backward <;> simpa [formulaPrinterTemplates] using ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
  apply symbolicAssignmentTemplate_sources
  intro s hs
  rcases symbolicFormulaCompile_sources p inputs base offset a ha s hs with h | ⟨i, h⟩
  · simpa [h] using hb
  · simpa [h] using hi i

theorem formulaPrinter_stable {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (r : NodePrinterRegisters R)
    (hb : r.SourceStable base) (hi : ∀ i, r.SourceStable (inputs i).source) :
    ∀ t ∈ formulaPrinterTemplates backward p inputs base offset, t.StableSources r := by
  intro t ht
  obtain ⟨hx, hy, hz⟩ := formulaPrinter_sources backward p inputs base offset r hb hi t ht
  exact ⟨⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩,
    ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1⟩, ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1⟩⟩

theorem formulaPrinter_operations_valid {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (r : NodePrinterRegisters R)
    (hr : r.Valid) (hb : r.SourceStable base) (hi : ∀ i, r.SourceStable (inputs i).source) :
    ∀ t ∈ formulaPrinterTemplates backward p inputs base offset,
      ∀ op ∈ t.ops r, op.Valid r.buf r.tmp := by
  intro t ht
  obtain ⟨hx, hy, hz⟩ := formulaPrinter_sources backward p inputs base offset r hb hi t ht
  simp_all [FixedNodeTemplate.ops, nodeFieldOperations, GeneratorOperation.Valid, AffineAtom.Valid,
    NodePrinterRegisters.Valid, NodePrinterRegisters.SourceStable]

end ShiReversibleGenerator
