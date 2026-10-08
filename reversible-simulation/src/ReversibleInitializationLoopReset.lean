import ReversibleConstantComponentClock

set_option autoImplicit false
namespace ShiReversibleGenerator

def initializationLoopReset : List InitializationRegister := [.inr 0, .inr 11]

theorem initializationLoopReset_counters (cs : InitializationRegister → Nat) :
    cleanupCounters initializationLoopReset cs = Function.update (Function.update cs (.inr 0) 0) (.inr 11) 0 := rfl

theorem initializationLoopReset_metadata (cs : InitializationRegister → Nat) (r : WorkspaceRegister) :
    cleanupCounters initializationLoopReset cs (.inl r) = cs (.inl r) := by
  simp [initializationLoopReset_counters]

theorem initializationLoopReset_index (cs : InitializationRegister → Nat) :
    cleanupCounters initializationLoopReset cs (.inr 0) = 0 := by
  simp [initializationLoopReset_counters]

theorem initializationLoopReset_remaining (cs : InitializationRegister → Nat) :
    cleanupCounters initializationLoopReset cs (.inr 11) = 0 := by
  simp [initializationLoopReset_counters]

theorem initializationLoopReset_layers (cs : InitializationRegister → Nat) :
    cleanupCounters initializationLoopReset cs (.inr 10) = cs (.inr 10) := by
  simp [initializationLoopReset_counters]

theorem initializationLoopReset_budget (cs : InitializationRegister → Nat) (bound : Nat)
    (h : CounterBudget cs (.inr 10) bound) :
    CounterBudget (cleanupCounters initializationLoopReset cs) (.inr 10) bound := by
  rw [initializationLoopReset_counters]
  exact (h.update (.inr 0) 0 (Nat.zero_le bound)).update (.inr 11) 0 (Nat.zero_le bound)

theorem initializationLoopReset_steps (cs : InitializationRegister → Nat) :
    cleanupSteps initializationLoopReset cs = 2 * cs (.inr 0) + 2 * cs (.inr 11) + 2 := by
  simp [initializationLoopReset, cleanupSteps]
  omega

theorem initializationLoopReset_clock (budget : Polynomial Nat) (n : Nat)
    (cs : InitializationRegister → Nat) (h : CounterBudget cs (.inr 10) (budget.eval n)) :
    cleanupSteps initializationLoopReset cs ≤ (Polynomial.C 4 * budget + Polynomial.C 2).eval n := by
  rw [initializationLoopReset_steps]
  have h0 := h (.inr 0) (by decide)
  have h11 := h (.inr 11) (by decide)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  omega

end ShiReversibleGenerator
