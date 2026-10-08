import ReversibleIndexExpressionProgram

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type}

/-- Actual expression execution has a polynomial clock from the real source-counter bounds. -/
theorem indexExpressionSteps_polynomial (p : TickIndexExpr) (capacity position target : R)
    (capacityBound positionBound targetBound : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : R → Nat),
      cs capacity ≤ capacityBound.eval n → cs position ≤ positionBound.eval n →
      cs target ≤ targetBound.eval n → indexExpressionSteps p capacity position target cs ≤ clock.eval n := by
  refine ⟨(Polynomial.C 2 * targetBound + Polynomial.C 1) +
    (Polynomial.C p.seed.coefficient *
      (Polynomial.C 7 * (capacityBound + positionBound) + Polynomial.C 2) +
      Polynomial.C p.seed.offset) + Polynomial.C (indexUpdateSteps p.updates), ?_⟩
  intro n cs hc hi ht
  have hs : cs (p.seed.source capacity position) ≤ capacityBound.eval n + positionBound.eval n :=
    (TickIndexSeed.source_bound _ _ _ _).trans (Nat.add_le_add hc hi)
  have hm := Nat.mul_le_mul_left p.seed.coefficient
    (show 7 * cs (p.seed.source capacity position) + 2 ≤
      7 * (capacityBound.eval n + positionBound.eval n) + 2 by omega)
  simp only [indexExpressionSteps, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  omega

/-- The computed target is bounded by the two input bounds and a syntax-dependent constant. -/
theorem indexExpressionValue_polynomial_bound (p : TickIndexExpr) (capacity position : Nat)
    (capacityBound positionBound : Polynomial Nat) (n : Nat)
    (hc : capacity ≤ capacityBound.eval n) (hi : position ≤ positionBound.eval n) :
    p.eval capacity position ≤ (capacityBound + positionBound + Polynomial.C p.allowance).eval n := by
  have h := p.eval_bound capacity position
  simp only [Polynomial.eval_add, Polynomial.eval_C]
  omega

end ShiReversibleGenerator
