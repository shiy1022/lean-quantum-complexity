import ReversibleFormulaSubstitution

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Finite classical choices made while printing, before the quantum circuit runs. -/
inductive DecisionTree (G α : Type) where
  | leaf : α → DecisionTree G α
  | branch : G → DecisionTree G α → DecisionTree G α → DecisionTree G α

variable {G α β γ : Type}

def DecisionTree.eval (test : G → Bool) : DecisionTree G α → α
  | .leaf a => a
  | .branch g y n => if test g then y.eval test else n.eval test

def DecisionTree.map (f : α → β) : DecisionTree G α → DecisionTree G β
  | .leaf a => .leaf (f a)
  | .branch g y n => .branch g (y.map f) (n.map f)

def DecisionTree.bind (f : α → DecisionTree G β) : DecisionTree G α → DecisionTree G β
  | .leaf a => f a
  | .branch g y n => .branch g (y.bind f) (n.bind f)

def DecisionTree.combine (f : α → β → γ) (p : DecisionTree G α) (q : DecisionTree G β) :
    DecisionTree G γ := p.bind (fun a => q.map (f a))

theorem DecisionTree.eval_map (p : DecisionTree G α) (f : α → β) (test : G → Bool) :
    (p.map f).eval test = f (p.eval test) := by
  induction p with
  | leaf a => rfl
  | branch g y n ihy ihn =>
    cases h : test g <;> simp [DecisionTree.map, DecisionTree.eval, h, ihy, ihn]

theorem DecisionTree.eval_bind (p : DecisionTree G α) (f : α → DecisionTree G β) (test : G → Bool) :
    (p.bind f).eval test = (f (p.eval test)).eval test := by
  induction p with
  | leaf a => rfl
  | branch g y n ihy ihn =>
    cases h : test g <;> simp [DecisionTree.bind, DecisionTree.eval, h, ihy, ihn]

theorem DecisionTree.eval_combine (p : DecisionTree G α) (q : DecisionTree G β)
    (f : α → β → γ) (test : G → Bool) :
    (DecisionTree.combine f p q).eval test = f (p.eval test) (q.eval test) := by
  simp [DecisionTree.combine, DecisionTree.eval_bind, DecisionTree.eval_map]

def DecisionTree.leaves : DecisionTree G α → List α
  | .leaf a => [a]
  | .branch _ y n => y.leaves ++ n.leaves

theorem DecisionTree.eval_mem_leaves (p : DecisionTree G α) (test : G → Bool) :
    p.eval test ∈ p.leaves := by
  induction p with
  | leaf a => simp [DecisionTree.eval, DecisionTree.leaves]
  | branch g y n ihy ihn =>
    cases h : test g <;> simp [DecisionTree.eval, DecisionTree.leaves, h, ihy, ihn]

end ShiReversibleGenerator
