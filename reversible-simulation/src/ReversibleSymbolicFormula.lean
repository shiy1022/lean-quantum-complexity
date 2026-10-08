import ReversibleFormulaRaw

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula

structure SymbolicWire (R : Type) where
  source : R
  offset : Nat

def SymbolicWire.eval {R : Type} (w : SymbolicWire R) (cs : R → Nat) : Nat := cs w.source + w.offset

inductive SymbolicAssignment (R : Type) where
  | constant : SymbolicWire R → Bool → SymbolicAssignment R
  | copy : SymbolicWire R → SymbolicWire R → SymbolicAssignment R
  | neg : SymbolicWire R → SymbolicWire R → SymbolicAssignment R
  | conj : SymbolicWire R → SymbolicWire R → SymbolicWire R → SymbolicAssignment R

def SymbolicAssignment.eval {R : Type} (cs : R → Nat) : SymbolicAssignment R → RawAssignment
  | .constant t b => .constant (t.eval cs) b
  | .copy s t => .copy (s.eval cs) (t.eval cs)
  | .neg s t => .neg (s.eval cs) (t.eval cs)
  | .conj a b t => .conj (a.eval cs) (b.eval cs) (t.eval cs)

/-- Fixed formula shape; all changing addresses are register values plus fixed offsets. -/
def symbolicFormulaCompile {R ι : Type} (inputs : ι → SymbolicWire R) (base : R)
    (offset : Nat) : Formula ι → List (SymbolicAssignment R)
  | .constant b => [.constant ⟨base, offset⟩ b]
  | .input i => [.copy (inputs i) ⟨base, offset⟩]
  | .neg p => symbolicFormulaCompile inputs base offset p ++
      [.neg ⟨base, offset + (p.size - 1)⟩ ⟨base, offset + p.size⟩]
  | .conj p q => symbolicFormulaCompile inputs base offset p ++
      symbolicFormulaCompile inputs base (offset + p.size) q ++
      [.conj ⟨base, offset + (p.size - 1)⟩
        ⟨base, offset + p.size + (q.size - 1)⟩ ⟨base, offset + p.size + q.size⟩]

/-- No new formula evaluator: specialization is exactly the already checked raw compiler. -/
theorem symbolicFormulaCompile_eval {R ι : Type} (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (cs : R → Nat) :
    (symbolicFormulaCompile inputs base offset p).map (SymbolicAssignment.eval cs) =
      p.rawCompile (fun i => (inputs i).eval cs) (cs base + offset) := by
  induction p generalizing offset with
  | constant => rfl
  | input => rfl
  | neg p ih =>
      have hp : 1 ≤ p.size := p.size_pos
      simp only [symbolicFormulaCompile, List.map_append, ih, List.map_cons, List.map_nil,
        SymbolicAssignment.eval, SymbolicWire.eval, Formula.rawCompile, Formula.result]
      simp only [Nat.add_assoc]
      congr 3 <;> omega
  | conj p q ihp ihq =>
      have hp : 1 ≤ p.size := p.size_pos
      have hq : 1 ≤ q.size := q.size_pos
      simp only [symbolicFormulaCompile, List.map_append, ihp, ihq, List.map_cons, List.map_nil,
        SymbolicAssignment.eval, SymbolicWire.eval, Formula.rawCompile, Formula.result]
      simp only [Nat.add_assoc]
      congr 3 <;> omega

theorem symbolicFormulaCompile_length {R ι : Type} (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) :
    (symbolicFormulaCompile inputs base offset p).length = p.size := by
  induction p generalizing offset with
  | constant => rfl
  | input => rfl
  | neg p ih => simp [symbolicFormulaCompile, ih, Formula.size]
  | conj p q ihp ihq => simp [symbolicFormulaCompile, ihp, ihq, Formula.size, Nat.add_assoc]

end ShiReversibleGenerator
