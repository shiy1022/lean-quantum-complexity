import ReversibleGuardedProgramClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R α : Type} [DecidableEq R]

/-- Structural compilation of the whole fixed decision tree into finite actual counter instructions. -/
noncomputable def compileGuardedTree (r : GuardProgramRegisters R) (leaf : α → CounterProgramTemplate R) :
    DecisionTree TickIndexGuard α → CounterProgramTemplate R
  | .leaf a => leaf a
  | .branch g y n => guardedProgramTemplate r g (compileGuardedTree r leaf y) (compileGuardedTree r leaf n)

theorem compileGuardedTree_embeds (r : GuardProgramRegisters R) (leaf : α → CounterProgramTemplate R)
    (tree : DecisionTree TickIndexGuard α) (h : ∀ a ∈ tree.leaves, (leaf a).Embeds) :
    (compileGuardedTree r leaf tree).Embeds := by
  induction tree with
  | leaf a => exact h a (by simp [DecisionTree.leaves])
  | branch g y n ihy ihn =>
    apply guardedProgramTemplate_embeds
    · apply ihy; intro a ha; exact h a (by simp [DecisionTree.leaves, ha])
    · apply ihn; intro a ha; exact h a (by simp [DecisionTree.leaves, ha])

theorem compileGuardedTree_run (r : GuardProgramRegisters R) (leaf : α → CounterProgramTemplate R)
    (tree : DecisionTree TickIndexGuard α) (hr : r.Valid)
    (he : ∀ a ∈ tree.leaves, (leaf a).Embeds) (h : ∀ a ∈ tree.leaves, (leaf a).Runs) :
    (compileGuardedTree r leaf tree).Runs := by
  induction tree with
  | leaf a => exact h a (by simp [DecisionTree.leaves])
  | branch g y n ihy ihn =>
    apply guardedProgramTemplate_run r g _ _ hr
    · apply compileGuardedTree_embeds; intro a ha; exact he a (by simp [DecisionTree.leaves, ha])
    · apply ihy
      · intro a ha; exact he a (by simp [DecisionTree.leaves, ha])
      · intro a ha; exact h a (by simp [DecisionTree.leaves, ha])
    · apply ihn
      · intro a ha; exact he a (by simp [DecisionTree.leaves, ha])
      · intro a ha; exact h a (by simp [DecisionTree.leaves, ha])

theorem compileGuardedTree_bytes (r : GuardProgramRegisters R) (leaf : α → CounterProgramTemplate R)
    (tree : DecisionTree TickIndexGuard α) (cs : R → Nat) :
    (compileGuardedTree r leaf tree).bytes cs =
      (leaf (tree.eval (fun g => g.eval (cs r.capacity) (cs r.position)))).bytes cs := by
  induction tree with
  | leaf a => rfl
  | branch g y n ihy ihn =>
    cases h : g.eval (cs r.capacity) (cs r.position) <;>
      simp [compileGuardedTree, guardedProgramTemplate, DecisionTree.eval, h, ihy, ihn]

theorem compileGuardedTree_counters (r : GuardProgramRegisters R) (leaf : α → CounterProgramTemplate R)
    (tree : DecisionTree TickIndexGuard α) (cs : R → Nat) :
    (compileGuardedTree r leaf tree).counters cs =
      (leaf (tree.eval (fun g => g.eval (cs r.capacity) (cs r.position)))).counters cs := by
  induction tree with
  | leaf a => rfl
  | branch g y n ihy ihn =>
    cases h : g.eval (cs r.capacity) (cs r.position) <;>
      simp [compileGuardedTree, guardedProgramTemplate, DecisionTree.eval, h, ihy, ihn]

theorem compileGuardedTree_polynomial (r : GuardProgramRegisters R) (leaf : α → CounterProgramTemplate R)
    (tree : DecisionTree TickIndexGuard α) (hr : r.Valid) (bound : Polynomial Nat)
    (h : ∀ a ∈ tree.leaves, (leaf a).PolynomiallyTimed bound) :
    (compileGuardedTree r leaf tree).PolynomiallyTimed bound := by
  induction tree with
  | leaf a => exact h a (by simp [DecisionTree.leaves])
  | branch g y n ihy ihn =>
    apply guardedProgramTemplate_polynomial r g _ _ hr bound
    · apply ihy; intro a ha; exact h a (by simp [DecisionTree.leaves, ha])
    · apply ihn; intro a ha; exact h a (by simp [DecisionTree.leaves, ha])

end ShiReversibleGenerator
