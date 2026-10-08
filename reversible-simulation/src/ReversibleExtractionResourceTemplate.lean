import ReversibleExtractionResourcePrelude

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- One finite graph initializes all concrete coordinates and prints the complete original extraction forest. -/
noncomputable def extractionResourceTemplate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (backward : Bool) :=
  sequenceProgramTemplate (extractionResourceSetupTemplate tm backward)
    (extractionMasterLift (extractionCleanForestLoopTemplate tm e (tickSizeBound tm+1) backward))

theorem extractionResourceTemplate_embeds (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (backward : Bool) :
    (extractionResourceTemplate tm e backward).Embeds :=
  sequenceProgramTemplate_embeds _ _ (extractionResourceSetupTemplate_embeds tm backward)
    (extractionMasterLift_embeds _)

theorem extractionResourceTemplate_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (backward : Bool) :
    (extractionResourceTemplate tm e backward).Runs :=
  sequenceProgramTemplate_run _ _ (extractionResourceSetupTemplate_embeds tm backward)
    (extractionResourceSetupTemplate_run tm backward)
    (extractionMasterLift_run _ (extractionCleanForestLoopTemplate_embeds tm e _ backward)
      (extractionCleanForestLoopTemplate_run tm e _ backward))

theorem extractionResourceTemplate_ready (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool) (backward : Bool)
    (cs : ExtractionMasterRegister → Nat) : (extractionResourceTemplate tm e backward).ready cs := by
  refine ⟨extractionResourceSetupTemplate_ready tm backward cs,?_⟩
  change (extractionCleanForestLoopTemplate tm e (tickSizeBound tm+1) backward).ready
    (fun q => (extractionResourceSetupTemplate tm backward).counters cs (.inr q))
  exact extractionCleanForestLoopTemplate_ready tm e _ backward _

theorem extractionResourceTemplate_resources (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (bound : Polynomial Nat) :
    (extractionResourceTemplate tm e backward).CounterBound bound ∧
      (extractionResourceTemplate tm e backward).PolynomiallyTimed bound := by
  obtain ⟨⟨middle,hm⟩,ht⟩ := extractionResourceSetupTemplate_resources tm backward bound
  have hr := extractionMasterLift_polynomial _ middle
    (extractionCleanForestLoopTemplate_resources tm e (tickSizeBound tm+1) backward middle).2
  obtain ⟨final,hf⟩ := extractionMasterLift_budget _ middle
    (extractionCleanForestLoopTemplate_resources tm e (tickSizeBound tm+1) backward middle).1
  exact ⟨⟨final,fun n cs hb q => hf n _ (hm n cs hb) q⟩,
    sequenceProgramTemplate_polynomial _ _ bound middle ht (fun n cs hb _ => hm n cs hb) hr⟩

end ShiReversibleGenerator
