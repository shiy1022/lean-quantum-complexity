import ReversibleOutputCopyLoopPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem outputCopyStepTemplate_counter_budget (cs : OutputCopyRegister → Nat) (bound : Nat)
    (hb : CounterBudget cs 2 bound) : CounterBudget (outputCopyStepTemplate.counters cs) 2 bound := by
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h3 := hb 3 (by decide)
  have h4 := hb 4 (by decide)
  have h5 := hb 5 (by decide)
  have h6 := hb 6 (by decide)
  have h7 := hb 7 (by decide)
  have h8 := hb 8 (by decide)
  have h9 := hb 9 (by decide)
  intro q hq
  rw [outputCopyStepTemplate_counters]
  fin_cases q <;> simp at hq ⊢
  all_goals omega

theorem outputCopyStepTemplate_cost_bound (cs : OutputCopyRegister → Nat) (bound : Nat)
    (hb : CounterBudget cs 2 bound) : outputCopyStepTemplate.steps cs ≤ 33*bound+21 := by
  rw [outputCopyStepTemplate_steps]
  have h0 := hb 0 (by decide)
  have h1 := hb 1 (by decide)
  have h5 := hb 5 (by decide)
  have h7 := hb 7 (by decide)
  omega

/-- The actual loop clock counts every test/decrement and every printed copy instruction. -/
theorem outputCopyLoopTemplate_polynomial (bound : Polynomial Nat) :
    outputCopyLoopTemplate.PolynomiallyTimed bound := by
  have h : ∀ k (cs : OutputCopyRegister → Nat) B,CounterBudget cs 2 B → k ≤ B →
      descendingTemplateSteps outputCopyStepTemplate 6 k cs ≤ k*(33*B+23)+1 := by
    intro k
    induction k with
    | zero => intro cs B hb hk; simp [descendingTemplateSteps]
    | succ k ih =>
        intro cs B hb hk
        have hu := hb.update (6 : OutputCopyRegister) k (by omega : k ≤ B)
        have hcost := outputCopyStepTemplate_cost_bound (Function.update cs 6 k) B hu
        have hnext := ih (outputCopyStepTemplate.counters (Function.update cs 6 k)) B
          (outputCopyStepTemplate_counter_budget _ _ hu) (by omega)
        rw [descendingTemplateSteps]
        rw [Nat.succ_mul]
        omega
  refine ⟨bound*(Polynomial.C 33*bound+Polynomial.C 23)+Polynomial.C 1,?_⟩
  intro n cs hb hr
  have hk := hb (6 : OutputCopyRegister)
  have hc := h (cs 6) cs (bound.eval n) (fun q _ => hb q) hk
  have hm := Nat.mul_le_mul_right (33*bound.eval n+23) hk
  simp only [outputCopyLoopTemplate,descendingProgramTemplate,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  omega

end ShiReversibleGenerator
