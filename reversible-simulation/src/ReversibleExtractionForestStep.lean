import ReversibleExtractionForestLeaf
import ReversibleExtractionForestRetreat
import ReversibleExtractionForestAdvance
import ReversibleDecrementProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Forward output emission descends before printing; inverse emission ascends after printing. -/
noncomputable def extractionForestStepPrograms (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : List (CounterProgramTemplate ExtractionForestRegister) :=
  if backward then [extractionForestLeafTemplate tm e stride true,extractionForestAdvanceTemplate]
  else [extractionForestRetreatTemplate,extractionForestLeafTemplate tm e stride false,decrementProgramTemplate 1]

noncomputable def extractionForestStepTemplate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) := listProgramTemplate (extractionForestStepPrograms tm e stride backward)

theorem extractionForestStepTemplate_embeds (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionForestStepTemplate tm e stride backward).Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  cases backward <;> simp only [extractionForestStepPrograms,Bool.false_eq_true,if_true,if_false,List.mem_cons,List.not_mem_nil,or_false] at hp
  · rcases hp with rfl | rfl | rfl
    · exact extractionForestRetreatTemplate_embeds
    · exact extractionForestLeafTemplate_embeds tm e stride false
    · exact decrementProgramTemplate_embeds _
  · rcases hp with rfl | rfl
    · exact extractionForestLeafTemplate_embeds tm e stride true
    · exact extractionForestAdvanceTemplate_embeds

theorem extractionForestStepTemplate_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionForestStepTemplate tm e stride backward).Runs := by
  apply listProgramTemplate_run
  · intro p hp
    cases backward <;> simp only [extractionForestStepPrograms,Bool.false_eq_true,if_true,if_false,List.mem_cons,List.not_mem_nil,or_false] at hp
    · rcases hp with rfl | rfl | rfl
      · exact extractionForestRetreatTemplate_embeds
      · exact extractionForestLeafTemplate_embeds tm e stride false
      · exact decrementProgramTemplate_embeds _
    · rcases hp with rfl | rfl
      · exact extractionForestLeafTemplate_embeds tm e stride true
      · exact extractionForestAdvanceTemplate_embeds
  · intro p hp
    cases backward <;> simp only [extractionForestStepPrograms,Bool.false_eq_true,if_true,if_false,List.mem_cons,List.not_mem_nil,or_false] at hp
    · rcases hp with rfl | rfl | rfl
      · exact extractionForestRetreatTemplate_run
      · exact extractionForestLeafTemplate_run tm e stride false
      · exact decrementProgramTemplate_run _
    · rcases hp with rfl | rfl
      · exact extractionForestLeafTemplate_run tm e stride true
      · exact extractionForestAdvanceTemplate_run

theorem extractionForestStepTemplate_ready (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionForestStepTemplate tm e stride backward).ready cs := by
  cases backward
  · exact ⟨extractionForestRetreatTemplate_ready cs,extractionForestLeafTemplate_ready tm e stride false _,trivial,trivial⟩
  · exact ⟨extractionForestLeafTemplate_ready tm e stride true cs,extractionForestAdvanceTemplate_ready _,trivial⟩

theorem extractionForestStepTemplate_resources (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (extractionForestStepTemplate tm e stride backward).CounterBound bound ∧
      (extractionForestStepTemplate tm e stride backward).PolynomiallyTimed bound := by
  apply listProgramTemplate_polynomial_certificate
  · intro p hp b
    cases backward <;> simp only [extractionForestStepPrograms,Bool.false_eq_true,if_true,if_false,List.mem_cons,List.not_mem_nil,or_false] at hp
    · rcases hp with rfl | rfl | rfl
      · exact (extractionForestRetreatTemplate_resources b).2
      · exact (extractionForestLeafTemplate_resources tm e stride false b).2
      · exact decrementProgramTemplate_polynomial _ b
    · rcases hp with rfl | rfl
      · exact (extractionForestLeafTemplate_resources tm e stride true b).2
      · exact (extractionForestAdvanceTemplate_resources b).2
  · intro p hp b
    cases backward <;> simp only [extractionForestStepPrograms,Bool.false_eq_true,if_true,if_false,List.mem_cons,List.not_mem_nil,or_false] at hp
    · rcases hp with rfl | rfl | rfl
      · exact (extractionForestRetreatTemplate_resources b).1
      · exact (extractionForestLeafTemplate_resources tm e stride false b).1
      · refine ⟨b,?_⟩
        intro n cs hb q
        have hq := hb q
        have h1 := hb 1
        simp only [decrementProgramTemplate,Function.update_apply]
        split_ifs <;> omega
    · rcases hp with rfl | rfl
      · exact (extractionForestLeafTemplate_resources tm e stride true b).1
      · exact (extractionForestAdvanceTemplate_resources b).1

end ShiReversibleGenerator
