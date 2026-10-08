import ReversibleStridedPrinterCounterBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM
variable {R α : Type} [DecidableEq R]

theorem compileGuardedTree_counter_bound (r : GuardProgramRegisters R)
    (leaf : α → CounterProgramTemplate R) (tree : DecisionTree TickIndexGuard α) (bound : Polynomial Nat)
    (h : ∀ a ∈ tree.leaves, ∃ budget : Polynomial Nat,
      ∀ n (cs : R → Nat), (∀ q, cs q ≤ bound.eval n) → ∀ q, (leaf a).counters cs q ≤ budget.eval n) :
    ∃ budget : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q, cs q ≤ bound.eval n) →
      ∀ q, (compileGuardedTree r leaf tree).counters cs q ≤ budget.eval n := by
  induction tree with
  | leaf a => exact h a (by simp [DecisionTree.leaves])
  | branch g y z ihy ihz =>
    obtain ⟨yb, hy⟩ := ihy (fun a ha => h a (by simp [DecisionTree.leaves, ha]))
    obtain ⟨zb, hz⟩ := ihz (fun a ha => h a (by simp [DecisionTree.leaves, ha]))
    refine ⟨yb + zb, ?_⟩
    intro n cs hc q
    change (if g.eval (cs r.capacity) (cs r.position) then
      (compileGuardedTree r leaf y).counters cs else (compileGuardedTree r leaf z).counters cs) q ≤ _
    split
    · simpa only [Polynomial.eval_add] using (hy n cs hc q).trans (Nat.le_add_right _ _)
    · simpa only [Polynomial.eval_add] using (hz n cs hc q).trans (Nat.le_add_left _ _)

theorem stridedSharedFixedGuardedEmitter_counter_bound {tm : Turing.FinTM2}
    (supply tree : TickGuardFormula tm) (inputStride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    ∃ budget : Polynomial Nat, ∀ n (cs : FixedLeafRegister supply → Nat),
      (∀ q, cs q ≤ bound.eval n) →
      ∀ q, (stridedSharedFixedGuardedEmitter supply tree inputStride backward).counters cs q ≤ budget.eval n := by
  apply compileGuardedTree_counter_bound
  intro p hp
  apply stridedBindingPrinterTemplate_counter_bound
  exact leafInputBindingTasks_valid tm (fixedLeafBindingRegisters supply) p (fixedLeafSlot supply p)
    (fun i => fixedLeafSlot_valid supply p i)

end ShiReversibleGenerator
