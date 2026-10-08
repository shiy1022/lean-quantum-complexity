import ReversibleGuardedProgramRun

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

def CounterProgramTemplate.PolynomiallyTimed (p : CounterProgramTemplate R) (bound : Polynomial Nat) : Prop :=
  ∃ clock : Polynomial Nat, ∀ n (cs : R → Nat), (∀ q, cs q ≤ bound.eval n) →
    p.ready cs → p.steps cs ≤ clock.eval n

theorem guardedProgramTemplate_polynomial (r : GuardProgramRegisters R) (g : TickIndexGuard)
    (y n : CounterProgramTemplate R) (hr : r.Valid) (bound : Polynomial Nat)
    (hy : y.PolynomiallyTimed bound) (hn : n.PolynomiallyTimed bound) :
    (guardedProgramTemplate r g y n).PolynomiallyTimed bound := by
  obtain ⟨cy, hy⟩ := hy
  obtain ⟨cn, hn⟩ := hn
  obtain ⟨cg, hg⟩ := indexGuardSteps_polynomial g r.capacity r.position r.left r.right
    hr.capacity_left hr.position_left hr.left_right bound bound
  refine ⟨cg + cy + cn, ?_⟩
  intro k cs hb hready
  rcases hready with ⟨hl, hr, hx, hyr, hnr⟩
  have hg' := hg k cs (hb r.capacity) (hb r.position) hl hr
  have hy' := hy k cs hb hyr
  have hn' := hn k cs hb hnr
  simp only [guardedProgramTemplate, Polynomial.eval_add]
  split <;> omega

end ShiReversibleGenerator
