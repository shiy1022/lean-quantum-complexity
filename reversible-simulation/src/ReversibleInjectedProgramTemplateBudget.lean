import ReversibleTemplateRegisterInjectionRun
import ReversibleProgramTemplateListBudget

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R S : Type} [DecidableEq R] [DecidableEq S]

/-- A finite injected component preserves polynomial bounds inside and outside its private block. -/
theorem injectProgramTemplate_budget (p : CounterProgramTemplate R) (f : R → S)
    (hf : Function.Injective f) (branch : R) (bound : Polynomial Nat) (hp : p.CounterBound bound) :
    (injectProgramTemplate p f branch).CounterBound bound := by
  classical
  obtain ⟨after,ha⟩ := hp
  refine ⟨after+bound,?_⟩
  intro n cs hb q
  change injectedTemplateCounters f cs (p.counters (fun r => cs (f r))) q ≤ (after+bound).eval n
  simp only [Polynomial.eval_add]
  by_cases h : ∃ r,f r=q
  · obtain ⟨r,rfl⟩ := h
    rw [injectedTemplateCounters_pull _ hf]
    exact (ha n _ (fun r => hb (f r)) r).trans (Nat.le_add_right _ _)
  · rw [injectedTemplateCounters_outside _ _ _ _ (by intro r hr; exact h ⟨r,hr⟩)]
    exact (hb q).trans (Nat.le_add_left _ _)

end ShiReversibleGenerator
