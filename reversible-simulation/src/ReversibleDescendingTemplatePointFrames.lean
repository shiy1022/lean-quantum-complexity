import ReversibleDescendingProgramTemplate

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- A pointwise register frame survives every iteration and the final loop-counter reset. -/
theorem descendingTemplateCounters_point_frame (p : CounterProgramTemplate R) (remaining q : R)
    (hq : q ≠ remaining) (hp : ∀ cs,p.counters cs q=cs q) (k : Nat) (cs : R → Nat) :
    descendingTemplateCounters p remaining k cs q=cs q := by
  induction k generalizing cs with
  | zero => rfl
  | succ k ih =>
    rw [descendingTemplateCounters,ih,hp,Function.update_of_ne hq]

theorem descendingProgramTemplate_point_frame (p : CounterProgramTemplate R) (remaining q : R)
    (hq : q ≠ remaining) (hp : ∀ cs,p.counters cs q=cs q) (cs : R → Nat) :
    (descendingProgramTemplate p remaining).counters cs q=cs q := by
  change Function.update (descendingTemplateCounters p remaining (cs remaining) cs) remaining 0 q=cs q
  rw [Function.update_of_ne hq,descendingTemplateCounters_point_frame p remaining q hq hp]

end ShiReversibleGenerator
