import ReversibleProgramTemplateList

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

def CounterProgramTemplate.CounterBound (p : CounterProgramTemplate R) (bound : Polynomial Nat) : Prop :=
  ∃ budget : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q, cs q ≤ bound.eval n) →
    ∀ q, p.counters cs q ≤ budget.eval n

/-- A fixed finite list of actual programs preserves polynomial counter bounds and runtime. -/
theorem listProgramTemplate_polynomial_certificate (ps : List (CounterProgramTemplate R))
    (ht : ∀ p ∈ ps, ∀ bound, p.PolynomiallyTimed bound)
    (hb : ∀ p ∈ ps, ∀ bound, p.CounterBound bound) (bound : Polynomial Nat) :
    (listProgramTemplate ps).CounterBound bound ∧ (listProgramTemplate ps).PolynomiallyTimed bound := by
  induction ps generalizing bound with
  | nil =>
    refine ⟨⟨bound, by intro n cs hc q; exact hc q⟩, 0, ?_⟩
    intro n cs hc hr
    simp [listProgramTemplate, identityProgramTemplate]
  | cons p ps ih =>
    obtain ⟨afterBudget, ha⟩ := hb p (by simp) bound
    obtain ⟨hb', ht'⟩ := ih (fun q hq => ht q (by simp [hq]))
      (fun q hq => hb q (by simp [hq])) afterBudget
    obtain ⟨finalBudget, hf⟩ := hb'
    refine ⟨⟨finalBudget, ?_⟩, ?_⟩
    · intro n cs hc q
      exact hf n (p.counters cs) (ha n cs hc) q
    · exact sequenceProgramTemplate_polynomial p (listProgramTemplate ps) bound afterBudget
        (ht p (by simp) bound) (fun n cs hc _ => ha n cs hc) ht'

end ShiReversibleGenerator
