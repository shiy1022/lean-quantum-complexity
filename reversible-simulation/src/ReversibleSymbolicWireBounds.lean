import ReversiblePaddedFormulaPrinterRun
import ReversiblePrinterFieldBounds

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula
variable {R : Type} [DecidableEq R]

def SymbolicAssignment.WiresBound (cs : R → Nat) (bound : Nat) : SymbolicAssignment R → Prop
  | .constant t _ => t.eval cs ≤ bound
  | .copy s t | .neg s t => s.eval cs ≤ bound ∧ t.eval cs ≤ bound
  | .conj s u t => s.eval cs ≤ bound ∧ u.eval cs ≤ bound ∧ t.eval cs ≤ bound

theorem symbolicFormulaCompile_wires_bound {ι : Type} (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (cs : R → Nat) (bound : Nat)
    (hi : ∀ i, (inputs i).eval cs ≤ bound) (hb : cs base + offset + p.size ≤ bound)
    (a : SymbolicAssignment R) (ha : a ∈ symbolicFormulaCompile inputs base offset p) :
    a.WiresBound cs bound := by
  induction p generalizing offset a with
  | constant b =>
      simp only [symbolicFormulaCompile, List.mem_singleton] at ha
      subst a
      simp only [SymbolicAssignment.WiresBound, SymbolicWire.eval]
      simp only [Formula.size] at hb
      omega
  | input i =>
      simp only [symbolicFormulaCompile, List.mem_singleton] at ha
      subst a
      refine ⟨hi i, ?_⟩
      simp only [SymbolicWire.eval]
      simp only [Formula.size] at hb
      omega
  | neg p ih =>
      simp only [symbolicFormulaCompile, List.mem_append, List.mem_singleton] at ha
      simp only [Formula.size] at hb
      rcases ha with ha | rfl
      · exact ih offset (by omega) a ha
      · simp only [SymbolicAssignment.WiresBound, SymbolicWire.eval]
        constructor <;> omega
  | conj p q ihp ihq =>
      simp only [symbolicFormulaCompile, List.mem_append, List.mem_singleton] at ha
      simp only [Formula.size] at hb
      rcases ha with (ha | ha) | rfl
      · exact ihp offset (by omega) a ha
      · exact ihq (offset + p.size) (by omega) a ha
      · simp only [SymbolicAssignment.WiresBound, SymbolicWire.eval]
        refine ⟨?_, ?_, ?_⟩ <;> omega

theorem symbolicAssignmentTemplate_wires_bound (backward : Bool) (a : SymbolicAssignment R)
    (cs : R → Nat) (bound : Nat) (ha : a.WiresBound cs bound) :
    (symbolicAssignmentTemplate backward a).x.eval cs ≤ bound ∧
    (symbolicAssignmentTemplate backward a).y.eval cs ≤ bound ∧
    (symbolicAssignmentTemplate backward a).z.eval cs ≤ bound := by
  cases a <;> simp_all [symbolicAssignmentTemplate, SymbolicAssignment.WiresBound]

theorem paddedFormulaPrinter_wires_bound {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (result : SymbolicWire R)
    (cs : R → Nat) (bound : Nat) (hi : ∀ i, (inputs i).eval cs ≤ bound)
    (hb : cs base + offset + p.size ≤ bound) (hr : result.eval cs ≤ bound) :
    ∀ t ∈ paddedFormulaPrinterTemplates backward p inputs base offset result,
      t.x.eval cs ≤ bound ∧ t.y.eval cs ≤ bound ∧ t.z.eval cs ≤ bound := by
  intro t ht
  have hm : t ∈ (paddedFormulaSymbolicNodes p inputs base offset result).map (symbolicAssignmentTemplate backward) := by
    cases backward <;> simpa [paddedFormulaPrinterTemplates] using ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
  apply symbolicAssignmentTemplate_wires_bound
  simp only [paddedFormulaSymbolicNodes, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · exact symbolicFormulaCompile_wires_bound p inputs base offset cs bound hi hb a ha
  · refine ⟨?_, hr⟩
    simp only [SymbolicWire.eval]
    omega

theorem paddedFormulaPrinter_nonempty {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (result : SymbolicWire R) :
    paddedFormulaPrinterTemplates backward p inputs base offset result ≠ [] := by
  cases backward <;> simp [paddedFormulaPrinterTemplates, paddedFormulaSymbolicNodes]

end ShiReversibleGenerator
