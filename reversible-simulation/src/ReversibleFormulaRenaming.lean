import ReversibleSymbolicFormula

set_option autoImplicit false
namespace ShiReversibleFormula
variable {ι κ : Type}

def Formula.rename (f : ι → κ) : Formula ι → Formula κ
  | .constant b => .constant b
  | .input i => .input (f i)
  | .neg p => .neg (p.rename f)
  | .conj p q => .conj (p.rename f) (q.rename f)

theorem Formula.rename_eval (p : Formula ι) (f : ι → κ) (x : κ → Bool) :
    (p.rename f).eval x = p.eval (fun i => x (f i)) := by
  induction p <;> simp_all [Formula.rename, Formula.eval]

theorem Formula.rename_size (p : Formula ι) (f : ι → κ) : (p.rename f).size = p.size := by
  induction p <;> simp_all [Formula.rename, Formula.size]

theorem rename_disjoin (ps : List (Formula ι)) (f : ι → κ) :
    (disjoin ps).rename f = disjoin (ps.map (fun p => p.rename f)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      change (p.disj (disjoin ps)).rename f = (p.rename f).disj (disjoin (ps.map (fun p => p.rename f)))
      simp only [Formula.disj, Formula.rename, ih]

theorem rename_unaryTable {α β : Type} [Fintype α] [DecidableEq β]
    (g : α → β) (inputs : α → Formula ι) (b : β) (f : ι → κ) :
    (unaryTable g inputs b).rename f = unaryTable g (fun a => (inputs a).rename f) b := by
  simp [unaryTable, rename_disjoin, List.map_map, Function.comp_def, Formula.rename]

theorem Formula.rename_rawCompile (p : Formula ι) (f : ι → κ) (inputs : κ → Nat) (base : Nat) :
    (p.rename f).rawCompile inputs base = p.rawCompile (fun i => inputs (f i)) base := by
  induction p generalizing base <;>
    simp_all [Formula.rename, Formula.rawCompile, Formula.result, Formula.rename_size]

end ShiReversibleFormula

namespace ShiReversibleGenerator
open ShiReversibleFormula

theorem symbolicFormulaCompile_rename {R ι κ : Type} (p : Formula ι) (f : ι → κ)
    (inputs : κ → SymbolicWire R) (base : R) (offset : Nat) :
    symbolicFormulaCompile inputs base offset (p.rename f) =
      symbolicFormulaCompile (fun i => inputs (f i)) base offset p := by
  induction p generalizing offset <;>
    simp_all [Formula.rename, symbolicFormulaCompile, Formula.rename_size]

end ShiReversibleGenerator
