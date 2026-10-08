import ReversibleIndexGuardProgram

set_option autoImplicit false
namespace ShiReversibleGenerator
variable {R : Type} [DecidableEq R]

/-- A guard's actual two expression runs and comparison fit a polynomial clock. -/
theorem indexGuardSteps_polynomial (g : TickIndexGuard) (capacity position left right : R)
    (hcl : capacity ≠ left) (hpl : position ≠ left) (hlr : left ≠ right)
    (capacityBound positionBound : Polynomial Nat) :
    ∃ clock : Polynomial Nat, ∀ n (cs : R → Nat),
      cs capacity ≤ capacityBound.eval n → cs position ≤ positionBound.eval n →
      cs left = 0 → cs right = 0 → indexGuardSteps g capacity position left right cs ≤ clock.eval n := by
  classical
  obtain ⟨pl, hclockL⟩ := indexExpressionSteps_polynomial g.left capacity position left
    capacityBound positionBound (Polynomial.C 0)
  obtain ⟨pr, hclockR⟩ := indexExpressionSteps_polynomial g.right capacity position right
    capacityBound positionBound (Polynomial.C 0)
  let ql := capacityBound + positionBound + Polynomial.C g.left.allowance
  let qr := capacityBound + positionBound + Polynomial.C g.right.allowance
  refine ⟨(pl + pr) + Polynomial.C 4 * (ql + qr) + Polynomial.C 3, ?_⟩
  intro n cs hc hi hl hr
  let cs₁ := Function.update cs left (g.left.eval (cs capacity) (cs position))
  have hcap : cs₁ capacity = cs capacity := by simp [cs₁, hcl]
  have hpos : cs₁ position = cs position := by simp [cs₁, hpl]
  have hright : cs₁ right = 0 := by simp [cs₁, Ne.symm hlr, hr]
  have h₁ := hclockL n cs hc hi (by simp [hl])
  have h₂ := hclockR n cs₁ (by simpa [hcap] using hc) (by simpa [hpos] using hi) (by simp [hright])
  have hvl : g.left.eval (cs capacity) (cs position) ≤ ql.eval n :=
    indexExpressionValue_polynomial_bound g.left _ _ _ _ n hc hi
  have hvr : g.right.eval (cs capacity) (cs position) ≤ qr.eval n :=
    indexExpressionValue_polynomial_bound g.right _ _ _ _ n hc hi
  have hcmp := comparisonSteps_bound (g.left.eval (cs capacity) (cs position))
    (g.right.eval (cs capacity) (cs position))
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  change (indexExpressionSteps g.left capacity position left cs +
    indexExpressionSteps g.right capacity position right cs₁) +
    comparisonSteps (g.left.eval (cs capacity) (cs position)) (g.right.eval (cs capacity) (cs position)) ≤ _
  omega

end ShiReversibleGenerator
