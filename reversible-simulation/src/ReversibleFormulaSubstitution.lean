import ReversibleFormulaRenaming

set_option autoImplicit false
namespace ShiReversibleFormula
variable {ι κ : Type}

def Formula.substitute (f : ι → Formula κ) : Formula ι → Formula κ
  | .constant b => .constant b
  | .input i => f i
  | .neg p => .neg (p.substitute f)
  | .conj p q => .conj (p.substitute f) (q.substitute f)

theorem Formula.substitute_eval (p : Formula ι) (f : ι → Formula κ) (x : κ → Bool) :
    (p.substitute f).eval x = p.eval (fun i => (f i).eval x) := by
  induction p <;> simp_all [Formula.substitute, Formula.eval]

theorem Formula.substitute_disj (p q : Formula ι) (f : ι → Formula κ) :
    (p.disj q).substitute f = (p.substitute f).disj (q.substitute f) := by rfl

theorem substitute_disjoin (ps : List (Formula ι)) (f : ι → Formula κ) :
    (disjoin ps).substitute f = disjoin (ps.map (fun p => p.substitute f)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change (p.disj (disjoin ps)).substitute f = _
    rw [Formula.substitute_disj, ih]
    rfl

theorem substitute_unaryTable {α β : Type} [Fintype α] [DecidableEq β]
    (g : α → β) (inputs : α → Formula ι) (b : β) (f : ι → Formula κ) :
    (unaryTable g inputs b).substitute f = unaryTable g (fun a => (inputs a).substitute f) b := by
  simp [unaryTable, substitute_disjoin, List.map_map, Function.comp_def, Formula.substitute]

theorem Formula.substitute_inputs (p : Formula ι) : p.substitute Formula.input = p := by
  induction p <;> simp_all [Formula.substitute]

end ShiReversibleFormula
