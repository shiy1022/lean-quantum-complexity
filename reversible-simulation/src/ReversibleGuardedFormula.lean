import ReversibleDecisionTree

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula
variable {G ι κ : Type}

def guardedFormula (inputs : ι → DecisionTree G (Formula κ)) :
    Formula ι → DecisionTree G (Formula κ)
  | .constant b => .leaf (.constant b)
  | .input i => inputs i
  | .neg p => (guardedFormula inputs p).map Formula.neg
  | .conj p q => DecisionTree.combine Formula.conj (guardedFormula inputs p) (guardedFormula inputs q)

theorem guardedFormula_eval (p : Formula ι) (inputs : ι → DecisionTree G (Formula κ))
    (test : G → Bool) :
    (guardedFormula inputs p).eval test = p.substitute (fun i => (inputs i).eval test) := by
  induction p <;> simp_all [guardedFormula, DecisionTree.eval, DecisionTree.eval_map,
    DecisionTree.eval_combine, Formula.substitute]

noncomputable def guardedUnaryTable {α β : Type} [Fintype α] [DecidableEq β]
    (f : α → β) (inputs : α → DecisionTree G (Formula κ)) (b : β) : DecisionTree G (Formula κ) :=
  guardedFormula inputs (unaryTable f Formula.input b)

theorem guardedUnaryTable_eval {α β : Type} [Fintype α] [DecidableEq β]
    (f : α → β) (inputs : α → DecisionTree G (Formula κ)) (b : β) (test : G → Bool) :
    (guardedUnaryTable f inputs b).eval test = unaryTable f (fun a => (inputs a).eval test) b := by
  simp only [guardedUnaryTable, guardedFormula_eval, substitute_unaryTable, Formula.substitute]

noncomputable def guardedBinaryTable {α β γ : Type} [Fintype α] [Fintype β] [DecidableEq γ]
    (f : α → β → γ) (left : α → DecisionTree G (Formula κ))
    (right : β → DecisionTree G (Formula κ)) (c : γ) : DecisionTree G (Formula κ) :=
  guardedUnaryTable (fun ab : α × β => f ab.1 ab.2)
    (fun ab => DecisionTree.combine Formula.conj (left ab.1) (right ab.2)) c

theorem guardedBinaryTable_eval {α β γ : Type} [Fintype α] [Fintype β] [DecidableEq γ]
    (f : α → β → γ) (left : α → DecisionTree G (Formula κ))
    (right : β → DecisionTree G (Formula κ)) (c : γ) (test : G → Bool) :
    (guardedBinaryTable f left right c).eval test =
      binaryTable f (fun a => (left a).eval test) (fun b => (right b).eval test) c := by
  simp only [guardedBinaryTable, guardedUnaryTable_eval, DecisionTree.eval_combine, binaryTable]

end ShiReversibleGenerator
