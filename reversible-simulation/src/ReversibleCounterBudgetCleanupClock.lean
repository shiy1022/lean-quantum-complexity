import ReversibleDescendingTemplateCounterResult

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- Cleanup of address/control counters has a clock independent of the growing layer count. -/
theorem cleanupSteps_counterBudget_bound (clear : List R) (count : R) (cs : R → Nat) (bound : Nat)
    (h : CounterBudget cs count bound) (hn : count ∉ clear) :
    cleanupSteps clear cs ≤ clear.length*(2*bound+1) := by
  induction clear generalizing cs with
  | nil => simp [cleanupSteps]
  | cons q clear ih =>
    have hq : q ≠ count := by intro he; subst q; exact hn (by simp)
    have hr : count ∉ clear := fun hc => hn (by simp [hc])
    have hc := h q hq
    have hh := ih (Function.update cs q 0) (h.update q 0 (Nat.zero_le _)) hr
    simp only [cleanupSteps,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem cleanupSteps_counterBudget_polynomial (clear : List R) (count : R) (bound : Polynomial Nat)
    (hn : count ∉ clear) (n : Nat) (cs : R → Nat) (h : CounterBudget cs count (bound.eval n)) :
    cleanupSteps clear cs ≤ (Polynomial.C clear.length*(Polynomial.C 2*bound+Polynomial.C 1)).eval n := by
  simpa only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C]
    using cleanupSteps_counterBudget_bound clear count cs (bound.eval n) h hn

end ShiReversibleGenerator
