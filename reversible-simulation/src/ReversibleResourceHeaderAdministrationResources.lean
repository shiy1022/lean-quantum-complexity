import ReversibleResourceHeaderAdministration
import ReversibleCounterAffineOffsetCopyBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The four actual header arithmetic programs have polynomial instruction clocks and counter exits. -/
theorem resourceHeaderAdministrationTemplate_resources (bound : Polynomial Nat) :
    resourceHeaderAdministrationTemplate.CounterBound bound ∧
      resourceHeaderAdministrationTemplate.PolynomiallyTimed bound := by
  apply listProgramTemplate_polynomial_certificate
  · intro p hp b
    simp only [resourceHeaderAdministrationPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ b
    · exact counterAffineAccumulationProgramTemplate_polynomial _ _ b
    · exact decrementProgramTemplate_polynomial _ b
    · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ b
  · intro p hp b
    simp only [resourceHeaderAdministrationPrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact counterAffineOffsetCopyProgramTemplate_budget _ _ _ 0 0 b
    · refine ⟨Polynomial.C 2*b,?_⟩
      intro n cs hc q
      simpa only [Polynomial.eval_mul,Polynomial.eval_C] using
        counterAffineUnitAccumulationProgramTemplate_budget (.inr 9) (.inr 12) (.inr 5) cs (b.eval n) hc q
    · refine ⟨b,?_⟩
      intro n cs hc q
      change Function.update cs (.inr 12) (cs (.inr 12)-1) q ≤ b.eval n
      simp only [Function.update_apply]
      split_ifs
      · exact (Nat.sub_le _ _).trans (hc _)
      · exact hc q
    · exact counterAffineOffsetCopyProgramTemplate_budget _ _ _ 0 0 b

end ShiReversibleGenerator
