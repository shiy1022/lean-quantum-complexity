import ReversibleNaturalPayload

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula
variable {R : Type} [DecidableEq R]

def symbolicAssignmentTemplate (backward : Bool) : SymbolicAssignment R → FixedNodeTemplate R
  | .constant t b => ⟨if b then .one else .zero, t, t, t⟩
  | .copy s t => ⟨.copy, s, s, t⟩
  | .neg s t => ⟨if backward then .negateBackward else .negateForward, s, s, t⟩
  | .conj a b t => ⟨.conjunction, a, b, t⟩

def rawAssignmentPayload (backward : Bool) : RawAssignment → List Bool
  | .constant t b => assignmentPayload (if b then .one else .zero) t t t
  | .copy s t => assignmentPayload .copy s s t
  | .neg s t => assignmentPayload (if backward then .negateBackward else .negateForward) s s t
  | .conj a b t => assignmentPayload .conjunction a b t

theorem symbolicAssignmentTemplate_payload (backward : Bool) (a : SymbolicAssignment R) (cs : R → Nat) :
    (symbolicAssignmentTemplate backward a).payload cs = rawAssignmentPayload backward (a.eval cs) := by
  cases a <;> rfl

/-- Forward circuit payload prints nodes in descending order; uncomputation uses ascending order. -/
def formulaPrinterTemplates {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) : List (FixedNodeTemplate R) :=
  let nodes := (symbolicFormulaCompile inputs base offset p).map (symbolicAssignmentTemplate backward)
  if backward then nodes else nodes.reverse

/-- Exact bytes of the established raw compiler, with both computation orders. -/
theorem formulaPrinter_bytes {ι : Type} (backward : Bool) (p : Formula ι)
    (inputs : ι → SymbolicWire R) (base : R) (offset : Nat) (r : NodePrinterRegisters R)
    (hpq : r.p ≠ r.q) (hpr : r.p ≠ r.r) (hqr : r.q ≠ r.r)
    (hs : ∀ t ∈ formulaPrinterTemplates backward p inputs base offset, t.StableSources r)
    (cs : R → Nat) :
    fixedNodeBytes r (formulaPrinterTemplates backward p inputs base offset) cs =
      if backward then
        ((p.rawCompile (fun i => (inputs i).eval cs) (cs base + offset)).reverse.map
          (rawAssignmentPayload backward)).flatten
      else ((p.rawCompile (fun i => (inputs i).eval cs) (cs base + offset)).map
        (rawAssignmentPayload backward)).flatten := by
  rw [fixedNodeBytes_payloads r _ hpq hpr hqr hs]
  have hm : ((symbolicFormulaCompile inputs base offset p).map (symbolicAssignmentTemplate backward)).map
      (fun t => t.payload cs) =
      (p.rawCompile (fun i => (inputs i).eval cs) (cs base + offset)).map (rawAssignmentPayload backward) := by
    rw [← symbolicFormulaCompile_eval p inputs base offset cs]
    simp [List.map_map, Function.comp_def, symbolicAssignmentTemplate_payload]
  cases backward <;> simp only [formulaPrinterTemplates, Bool.false_eq_true, Bool.true_eq,
    if_false, if_true, List.reverse_reverse, List.map_reverse]
  all_goals rw [hm]
  all_goals rfl

end ShiReversibleGenerator
