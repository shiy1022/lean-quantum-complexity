import ReversibleExtractionForestLeafLoad
import ReversibleExtractionForestLiftBudget
import ReversibleExtractionInitializedPaddedLeaf

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- One actual output-forest leaf loads its dynamic padding bound and executes the initialized padded emitter. -/
noncomputable def extractionForestLeafTemplate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) :=
  sequenceProgramTemplate extractionForestLeafLoadTemplate
    (extractionForestLift (extractionInitializedPaddedLeafTemplate tm e stride backward))

theorem extractionForestLeafTemplate_embeds (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionForestLeafTemplate tm e stride backward).Embeds :=
  sequenceProgramTemplate_embeds _ _ extractionForestLeafLoadTemplate_embeds (extractionForestLift_embeds _)

theorem extractionForestLeafTemplate_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionForestLeafTemplate tm e stride backward).Runs :=
  sequenceProgramTemplate_run _ _ extractionForestLeafLoadTemplate_embeds extractionForestLeafLoadTemplate_run
    (extractionForestLift_run _ (extractionInitializedPaddedLeafTemplate_embeds tm e stride backward)
      (extractionInitializedPaddedLeafTemplate_run tm e stride backward))

theorem extractionForestLeafTemplate_ready (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionForestLeafTemplate tm e stride backward).ready cs :=
  ⟨extractionForestLeafLoadTemplate_ready cs,extractionInitializedPaddedLeafTemplate_ready tm e stride backward _⟩

theorem extractionForestLeafTemplate_resources (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (extractionForestLeafTemplate tm e stride backward).CounterBound bound ∧
      (extractionForestLeafTemplate tm e stride backward).PolynomiallyTimed bound := by
  obtain ⟨hb,ht⟩ := extractionInitializedPaddedLeafTemplate_resources tm e stride backward bound
  obtain ⟨final,hf⟩ := extractionForestLift_budget _ bound hb
  obtain ⟨hload,tload⟩ := extractionForestLeafLoadTemplate_resources bound
  obtain ⟨loadBound,hl⟩ := hload
  -- The load has the sharper identity bound proved directly above.
  have hloadExact : ∀ n cs,(∀ q,cs q ≤ bound.eval n) → ∀ q,extractionForestLeafLoadTemplate.counters cs q ≤ bound.eval n := by
    intro n cs hc q
    rw [extractionForestLeafLoadTemplate_counters]
    simp only [Function.update_apply,cleanupCounters_apply]
    have hq := hc q
    have hs := hc 27
    split_ifs <;> omega
  exact ⟨⟨final,fun n cs hc q => hf n _ (hloadExact n cs hc) q⟩,
    sequenceProgramTemplate_polynomial _ _ bound bound tload (fun n cs hc _ => hloadExact n cs hc)
      (extractionForestLift_polynomial _ bound ht)⟩

end ShiReversibleGenerator
