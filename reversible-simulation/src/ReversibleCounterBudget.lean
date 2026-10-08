import ReversibleCounterProgram

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- The layer counter has its own linear bound; all other counters share an address budget. -/
def CounterBudget (cs : R → Nat) (count : R) (bound : Nat) : Prop :=
  ∀ r, r ≠ count → cs r ≤ bound

theorem CounterBudget.update {cs : R → Nat} {count : R} {bound : Nat}
    (h : CounterBudget cs count bound) (target : R) (value : Nat) (hv : value ≤ bound) :
    CounterBudget (Function.update cs target value) count bound := by
  intro r hr
  by_cases ht : r = target
  · subst r; simpa using hv
  · simpa [ht] using h r hr

theorem CounterBudget.update_count {cs : R → Nat} {count : R} {bound : Nat}
    (h : CounterBudget cs count bound) (value : Nat) :
    CounterBudget (Function.update cs count value) count bound := by
  intro r hr
  simpa [hr] using h r hr

end ShiReversibleGenerator
