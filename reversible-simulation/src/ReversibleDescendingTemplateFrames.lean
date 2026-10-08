import ReversibleDescendingProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

theorem descendingTemplateCounters_other (p : CounterProgramTemplate R) (remaining q : R)
    (hne : q ≠ remaining) (hf : ∀ cs, p.counters cs q = cs q) (count : Nat) (cs : R → Nat) :
    descendingTemplateCounters p remaining count cs q = cs q := by
  induction count generalizing cs with
  | zero => rfl
  | succ k ih =>
    rw [descendingTemplateCounters,ih,hf]
    simp [hne]

theorem descendingProgramTemplate_other_frame (p : CounterProgramTemplate R) (remaining q : R)
    (hne : q ≠ remaining) (hf : ∀ cs, p.counters cs q = cs q) (cs : R → Nat) :
    (descendingProgramTemplate p remaining).counters cs q = cs q := by
  change Function.update (descendingTemplateCounters p remaining (cs remaining) cs) remaining 0 q = _
  rw [Function.update_of_ne hne,descendingTemplateCounters_other p remaining q hne hf]

/-- The loop wrapper clears its actual remaining counter on exit, including a zero-length traversal. -/
theorem descendingProgramTemplate_remaining_zero (p : CounterProgramTemplate R) (remaining : R) (cs : R → Nat) :
    (descendingProgramTemplate p remaining).counters cs remaining = 0 := by
  exact Function.update_self _ _ _

end ShiReversibleGenerator
