import ReversibleExtractionCleanForestStepMetadata

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Runtime output width drives a real finite descending loop in either emission direction. -/
noncomputable def extractionCleanForestLoopTemplate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) := descendingProgramTemplate (extractionCleanForestStepTemplate tm e stride backward) 26

theorem extractionCleanForestLoopTemplate_embeds (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionCleanForestLoopTemplate tm e stride backward).Embeds :=
  descendingProgramTemplate_embeds _ _ (extractionCleanForestStepTemplate_embeds tm e stride backward)

theorem extractionCleanForestLoopTemplate_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionCleanForestLoopTemplate tm e stride backward).Runs :=
  descendingProgramTemplate_run _ _ (extractionCleanForestStepTemplate_embeds tm e stride backward)
    (extractionCleanForestStepTemplate_run tm e stride backward)

theorem extractionCleanForestLoopTemplate_ready (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionCleanForestLoopTemplate tm e stride backward).ready cs := by
  have h : ∀ k (t : ExtractionForestRegister → Nat),descendingTemplateReady (extractionCleanForestStepTemplate tm e stride backward) 26 k t := by
    intro k
    induction k with
    | zero => intro t; trivial
    | succ k ih =>
      intro t
      refine ⟨extractionCleanForestStepTemplate_ready tm e stride backward _,?_,ih _⟩
      exact ((extractionCleanForestStepTemplate_metadata tm e stride backward _).2.2.2.2.1).trans (Function.update_self _ _ _)
  exact h _ cs

end ShiReversibleGenerator
