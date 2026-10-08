import ReversibleExtractionPaddedLeafSetup
import ReversibleExtractionPaddedLeafReady

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- A fixed finite graph computes its size and roots before emitting the padded extraction leaf. -/
noncomputable def extractionInitializedPaddedLeafTemplate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (backward : Bool) :=
  sequenceProgramTemplate (extractionPaddedLeafSetupTemplate tm) (extractionPaddedLeafTemplate tm e stride backward)

theorem extractionInitializedPaddedLeafTemplate_embeds (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (backward : Bool) :
    (extractionInitializedPaddedLeafTemplate tm e stride backward).Embeds :=
  sequenceProgramTemplate_embeds _ _ (extractionPaddedLeafSetupTemplate_embeds tm)
    (extractionPaddedLeafTemplate_embeds tm e stride backward)

theorem extractionInitializedPaddedLeafTemplate_run (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (backward : Bool) :
    (extractionInitializedPaddedLeafTemplate tm e stride backward).Runs :=
  sequenceProgramTemplate_run _ _ (extractionPaddedLeafSetupTemplate_embeds tm)
    (extractionPaddedLeafSetupTemplate_run tm) (extractionPaddedLeafTemplate_run tm e stride backward)

theorem extractionInitializedPaddedLeafTemplate_ready (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat) :
    (extractionInitializedPaddedLeafTemplate tm e stride backward).ready cs := by
  have hs := extractionPaddedLeafSetupTemplate_scratch tm cs
  exact ⟨extractionPaddedLeafSetupTemplate_ready tm cs,
    extractionPaddedLeafTemplate_ready tm e stride backward _ hs.2 hs.1⟩

theorem extractionInitializedPaddedLeafTemplate_resources (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (extractionInitializedPaddedLeafTemplate tm e stride backward).CounterBound bound ∧
      (extractionInitializedPaddedLeafTemplate tm e stride backward).PolynomiallyTimed bound := by
  obtain ⟨⟨middle,hm⟩,ht⟩ := extractionPaddedLeafSetupTemplate_resources tm bound
  obtain ⟨⟨final,hf⟩,hr⟩ := extractionPaddedLeafTemplate_resources tm e stride backward middle
  exact ⟨⟨final,fun n cs hb q => hf n _ (hm n cs hb) q⟩,
    sequenceProgramTemplate_polynomial _ _ bound middle ht (fun n cs hb _ => hm n cs hb) hr⟩

end ShiReversibleGenerator
