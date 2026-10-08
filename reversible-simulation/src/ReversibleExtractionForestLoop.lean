import ReversibleExtractionForestStepMetadata

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Runtime output width drives a real finite descending loop in either emission direction. -/
noncomputable def extractionForestLoopTemplate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) := descendingProgramTemplate (extractionForestStepTemplate tm e stride backward) 26

theorem extractionForestLoopTemplate_embeds (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionForestLoopTemplate tm e stride backward).Embeds :=
  descendingProgramTemplate_embeds _ _ (extractionForestStepTemplate_embeds tm e stride backward)

theorem extractionForestLoopTemplate_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionForestLoopTemplate tm e stride backward).Runs :=
  descendingProgramTemplate_run _ _ (extractionForestStepTemplate_embeds tm e stride backward)
    (extractionForestStepTemplate_run tm e stride backward)

theorem extractionForestLoopTemplate_ready (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionForestLoopTemplate tm e stride backward).ready cs := by
  have h : ∀ k (t : ExtractionForestRegister → Nat),descendingTemplateReady (extractionForestStepTemplate tm e stride backward) 26 k t := by
    intro k
    induction k with
    | zero => intro t; trivial
    | succ k ih =>
      intro t
      refine ⟨extractionForestStepTemplate_ready tm e stride backward _,?_,ih _⟩
      exact ((extractionForestStepTemplate_metadata tm e stride backward _).2.2.2.2.1).trans (Function.update_self _ _ _)
  exact h _ cs

end ShiReversibleGenerator
