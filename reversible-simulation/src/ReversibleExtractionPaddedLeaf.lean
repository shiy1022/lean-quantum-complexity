import ReversibleExtractionPaddedPass
import ReversibleExtractionPaddedRootCopy

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Reverse the execution order because runtime emission prepends each block to its output. -/
noncomputable def extractionPaddedLeafTemplate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : CounterProgramTemplate ExtractionPaddedRegister :=
  listProgramTemplate (if backward then [extractionPaddedPassTemplate tm e stride backward,extractionPaddedRootCopyTemplate]
    else [extractionPaddedRootCopyTemplate,extractionPaddedPassTemplate tm e stride backward])

theorem extractionPaddedLeafTemplate_embeds (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionPaddedLeafTemplate tm e stride backward).Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  cases backward <;> simp only [Bool.false_eq_true,if_false,if_true,List.mem_cons,List.not_mem_nil,or_false] at hp
  all_goals rcases hp with rfl | rfl
  all_goals first | exact extractionPaddedRootCopyTemplate_embeds | exact extractionPaddedPassTemplate_embeds tm e stride _

theorem extractionPaddedLeafTemplate_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionPaddedLeafTemplate tm e stride backward).Runs := by
  apply listProgramTemplate_run
  · intro p hp
    cases backward <;> simp only [Bool.false_eq_true,if_false,if_true,List.mem_cons,List.not_mem_nil,or_false] at hp
    all_goals rcases hp with rfl | rfl
    all_goals first | exact extractionPaddedRootCopyTemplate_embeds | exact extractionPaddedPassTemplate_embeds tm e stride _
  · intro p hp
    cases backward <;> simp only [Bool.false_eq_true,if_false,if_true,List.mem_cons,List.not_mem_nil,or_false] at hp
    all_goals rcases hp with rfl | rfl
    all_goals first | exact extractionPaddedRootCopyTemplate_run | exact extractionPaddedPassTemplate_run tm e stride _

theorem extractionPaddedLeafTemplate_resources (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (extractionPaddedLeafTemplate tm e stride backward).CounterBound bound ∧
      (extractionPaddedLeafTemplate tm e stride backward).PolynomiallyTimed bound := by
  apply listProgramTemplate_polynomial_certificate
  · intro p hp b
    cases backward <;> simp only [Bool.false_eq_true,if_false,if_true,List.mem_cons,List.not_mem_nil,or_false] at hp
    all_goals rcases hp with rfl | rfl
    all_goals first | exact (extractionPaddedRootCopyTemplate_resources b).2 | exact (extractionPaddedPassTemplate_resources tm e stride _ b).2
  · intro p hp b
    cases backward <;> simp only [Bool.false_eq_true,if_false,if_true,List.mem_cons,List.not_mem_nil,or_false] at hp
    all_goals rcases hp with rfl | rfl
    all_goals first | exact (extractionPaddedRootCopyTemplate_resources b).1 | exact (extractionPaddedPassTemplate_resources tm e stride _ b).1

end ShiReversibleGenerator
