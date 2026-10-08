import ReversiblePrinterFieldBounds
import ReversibleFormulaSources

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ShiReversibleGenerator
open ShiReversibleFormula
variable {R : Type} [DecidableEq R]

/-- Every formula node uses a bounded input or a wire inside the fixed formula block. -/
theorem symbolicFormulaCompile_fields_bound {ι : Type} (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (backward : Bool)
    (cs : R → Nat) (B : Nat) (hb : cs base ≤ B) (hi : ∀ i,(inputs i).eval cs ≤ B)
    (a : SymbolicAssignment R) (ha : a ∈ symbolicFormulaCompile inputs base offset p) :
    let t := symbolicAssignmentTemplate backward a
    t.x.eval cs ≤ B+offset+p.size ∧ t.y.eval cs ≤ B+offset+p.size ∧
      t.z.eval cs ≤ B+offset+p.size := by
  induction p generalizing offset a with
  | constant b =>
    simp only [symbolicFormulaCompile,List.mem_singleton] at ha
    subst a
    simp only [symbolicAssignmentTemplate,SymbolicWire.eval,Formula.size]
    omega
  | input i =>
    simp only [symbolicFormulaCompile,List.mem_singleton] at ha
    subst a
    have h := hi i
    simp only [symbolicAssignmentTemplate,SymbolicWire.eval,Formula.size] at *
    omega
  | neg p ih =>
    simp only [symbolicFormulaCompile,List.mem_append,List.mem_singleton] at ha
    rcases ha with ha | rfl
    · obtain ⟨hx,hy,hz⟩ := ih offset a ha
      simp only [Formula.size]
      exact ⟨by omega,by omega,by omega⟩
    · simp only [symbolicAssignmentTemplate,SymbolicWire.eval,Formula.size]
      omega
  | conj p q ihp ihq =>
    simp only [symbolicFormulaCompile,List.mem_append,List.mem_singleton] at ha
    rcases ha with (ha | ha) | rfl
    · obtain ⟨hx,hy,hz⟩ := ihp offset a ha
      simp only [Formula.size]
      exact ⟨by omega,by omega,by omega⟩
    · obtain ⟨hx,hy,hz⟩ := ihq (offset+p.size) a ha
      simp only [Formula.size]
      exact ⟨by omega,by omega,by omega⟩
    · simp only [symbolicAssignmentTemplate,SymbolicWire.eval,Formula.size]
      omega

/-- A nonempty formula printer overwrites old fields with polynomially bounded addresses. -/
theorem formulaPrinter_counters_fields_bound {ι : Type} (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (backward : Bool)
    (r : NodePrinterRegisters R)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hcp : r.count ≠ r.p) (hcq : r.count ≠ r.q) (hcr : r.count ≠ r.r)
    (hsb : r.SourceStable base) (hsi : ∀ i,r.SourceStable (inputs i).source)
    (cs : R → Nat) (B : Nat) (hb : cs base ≤ B) (hi : ∀ i,(inputs i).eval cs ≤ B) :
    fixedNodeCounters r (formulaPrinterTemplates backward p inputs base offset) cs r.p ≤ B+offset+p.size ∧
    fixedNodeCounters r (formulaPrinterTemplates backward p inputs base offset) cs r.q ≤ B+offset+p.size ∧
    fixedNodeCounters r (formulaPrinterTemplates backward p inputs base offset) cs r.r ≤ B+offset+p.size := by
  apply fixedNodeCounters_fields_bound r _ hpq hpr hqr hcp hcq hcr
  · exact formulaPrinter_stable backward p inputs base offset r hsb hsi
  · have hl := symbolicFormulaCompile_length p inputs base offset
    have hp := p.size_pos
    intro he
    have : (formulaPrinterTemplates backward p inputs base offset).length=0 := by rw [he]; rfl
    cases backward <;> simp [formulaPrinterTemplates,hl] at this <;> omega
  · intro t ht
    have hm : t ∈ (symbolicFormulaCompile inputs base offset p).map (symbolicAssignmentTemplate backward) := by
      cases backward <;> simpa [formulaPrinterTemplates] using ht
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact symbolicFormulaCompile_fields_bound p inputs base offset backward cs B hb hi a ha

end ShiReversibleGenerator
