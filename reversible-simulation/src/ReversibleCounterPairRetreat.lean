import ReversibleDecrementProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

noncomputable def counterPairDecrementTemplate (a b : R) :=
  sequenceProgramTemplate (decrementProgramTemplate a) (decrementProgramTemplate b)

noncomputable def counterPairRetreatTemplate (a b remaining : R) :=
  descendingProgramTemplate (counterPairDecrementTemplate a b) remaining

theorem counterPairRetreatTemplate_embeds (a b remaining : R) :
    (counterPairRetreatTemplate a b remaining).Embeds :=
  descendingProgramTemplate_embeds _ _ (sequenceProgramTemplate_embeds _ _
    (decrementProgramTemplate_embeds a) (decrementProgramTemplate_embeds b))

theorem counterPairRetreatTemplate_run (a b remaining : R) :
    (counterPairRetreatTemplate a b remaining).Runs :=
  descendingProgramTemplate_run _ _ (sequenceProgramTemplate_embeds _ _
    (decrementProgramTemplate_embeds a) (decrementProgramTemplate_embeds b))
    (sequenceProgramTemplate_run _ _ (decrementProgramTemplate_embeds a)
      (decrementProgramTemplate_run a) (decrementProgramTemplate_run b))

theorem counterPairRetreatTemplate_ready (a b remaining : R) (ha : a ≠ remaining) (hb : b ≠ remaining)
    (cs : R → Nat) : (counterPairRetreatTemplate a b remaining).ready cs := by
  suffices h : ∀ k cs,descendingTemplateReady (counterPairDecrementTemplate a b) remaining k cs by
    exact h _ _
  intro k
  induction k with
  | zero => intro cs; trivial
  | succ k ih =>
    intro cs
    refine ⟨⟨trivial,trivial⟩,?_,ih _⟩
    simp [counterPairDecrementTemplate,sequenceProgramTemplate,decrementProgramTemplate,Ne.symm ha,Ne.symm hb]

theorem counterPairRetreatTemplate_steps (a b remaining : R) (cs : R → Nat) :
    (counterPairRetreatTemplate a b remaining).steps cs=4*cs remaining+1 := by
  suffices h : ∀ k cs,descendingTemplateSteps (counterPairDecrementTemplate a b) remaining k cs=4*k+1 by
    exact h _ _
  intro k
  induction k with
  | zero => intro cs; rfl
  | succ k ih =>
    intro cs
    rw [descendingTemplateSteps,ih]
    change 2+(1+1)+(4*k+1)=4*(k+1)+1
    omega

theorem counterPairRetreatTemplate_bytes (a b remaining : R) (cs : R → Nat) :
    (counterPairRetreatTemplate a b remaining).bytes cs=[] := by
  suffices h : ∀ k cs,descendingTemplateBytes (counterPairDecrementTemplate a b) remaining k cs=[] by
    exact h _ _
  intro k
  induction k with
  | zero => intro cs; rfl
  | succ k ih =>
    intro cs
    rw [descendingTemplateBytes,ih]
    rfl

/-- Every outer register is framed; the two targets subtract the real loop count. -/
theorem counterPairRetreatTemplate_counters (a b remaining : R) (hab : a ≠ b)
    (ha : a ≠ remaining) (hb : b ≠ remaining) (cs : R → Nat) :
    (counterPairRetreatTemplate a b remaining).counters cs=
      Function.update (Function.update (Function.update cs a (cs a-cs remaining)) b (cs b-cs remaining)) remaining 0 := by
  have h : ∀ k (t : R → Nat) q, q ≠ remaining →
      descendingTemplateCounters (counterPairDecrementTemplate a b) remaining k t q=
        if q=b then t b-k else if q=a then t a-k else t q := by
    intro k
    induction k with
    | zero =>
      intro t q hq
      by_cases hqb : q=b
      · subst q; simp [descendingTemplateCounters]
      · by_cases hqa : q=a
        · subst q; simp [descendingTemplateCounters,hqb]
        · simp [descendingTemplateCounters,hqb,hqa]
    | succ k ih =>
      intro t q hq
      rw [descendingTemplateCounters,ih _ q hq]
      by_cases hqb : q=b
      · subst q
        simp [counterPairDecrementTemplate,sequenceProgramTemplate,decrementProgramTemplate,Ne.symm hab,hb,Nat.sub_sub,Nat.add_comm]
      · by_cases hqa : q=a
        · subst q
          simp [hqb,counterPairDecrementTemplate,sequenceProgramTemplate,decrementProgramTemplate,hab,ha,Nat.sub_sub,Nat.add_comm]
        · simp [hqb,hqa,counterPairDecrementTemplate,sequenceProgramTemplate,decrementProgramTemplate,hq]
  funext q
  by_cases hq : q=remaining
  · subst q
    simp [counterPairRetreatTemplate,descendingProgramTemplate]
  · change Function.update (descendingTemplateCounters _ remaining (cs remaining) cs) remaining 0 q=_
    rw [Function.update_of_ne hq,h _ cs q hq]
    by_cases hqb : q=b
    · subst q; simp [hq]
    · by_cases hqa : q=a
      · subst q; simp [hq,hqb]
      · simp [hq,hqb,hqa]

theorem counterPairRetreatTemplate_polynomial (a b remaining : R) (bound : Polynomial Nat) :
    (counterPairRetreatTemplate a b remaining).PolynomiallyTimed bound := by
  refine ⟨Polynomial.C 4*bound+Polynomial.C 1,?_⟩
  intro n cs hb _
  rw [counterPairRetreatTemplate_steps]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 4 (hb remaining)) 1

end ShiReversibleGenerator
