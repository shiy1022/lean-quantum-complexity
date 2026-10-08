import ReversibleExtractionForwardClosingLoopResources
import ReversibleExtractionForwardPrefixFullCertificate
import ReversibleExtractionPassHandoff
import ReversibleExtractionTraversalLiftBudget
import ReversibleExtractionClosingStepFrames
import ReversibleExtractionForwardClosingSourceFrames
import ReversibleExtractionForwardClosingLoopReady

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Closing runs first; prepending the descending term-prefix pass assembles the original forward compiler. -/
noncomputable def extractionForwardPassTemplate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :=
  sequenceProgramTemplate (extractionTraversalLift (extractionForwardClosingLoopTemplate tm))
    (sequenceProgramTemplate extractionDescendingPassHandoffTemplate (extractionForwardPrefixLoopTemplate tm e stride))

theorem extractionForwardPassTemplate_embeds (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) : (extractionForwardPassTemplate tm e stride).Embeds :=
  sequenceProgramTemplate_embeds _ _ (extractionTraversalLift_embeds _)
    (sequenceProgramTemplate_embeds _ _ extractionDescendingPassHandoffTemplate_embeds
      (extractionForwardPrefixLoopTemplate_embeds tm e stride))

theorem extractionForwardPassTemplate_run (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) : (extractionForwardPassTemplate tm e stride).Runs :=
  sequenceProgramTemplate_run _ _ (extractionTraversalLift_embeds _)
    (extractionTraversalLift_run _ (extractionForwardClosingLoopTemplate_embeds tm)
      (extractionForwardClosingLoopTemplate_run tm))
    (sequenceProgramTemplate_run _ _ extractionDescendingPassHandoffTemplate_embeds
      extractionDescendingPassHandoffTemplate_run (extractionForwardPrefixLoopTemplate_run tm e stride))

theorem extractionForwardPassTemplate_ready (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (hb : cs 17=0) :
    (extractionForwardPassTemplate tm e stride).ready cs := by
  let t := (extractionTraversalLift (extractionForwardClosingLoopTemplate tm)).counters cs
  have ht : t 17=0 := (extractionForwardClosingLift_source_frame tm cs 17 (by simp)).trans hb
  refine ⟨?_,extractionDescendingPassHandoffTemplate_ready t,?_⟩
  · change (extractionForwardClosingLoopTemplate tm).ready (fun r => cs (extractionTermToTraversalRegister r))
    exact extractionForwardClosingLoopTemplate_ready tm _ hb
  · apply extractionForwardPrefixLoopTemplate_ready tm e stride
    simpa [extractionDescendingPassHandoffTemplate_counters,cleanupCounters_apply] using ht

theorem extractionForwardPassTemplate_resources (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (bound : Polynomial Nat) :
    (extractionForwardPassTemplate tm e stride).CounterBound bound ∧
      (extractionForwardPassTemplate tm e stride).PolynomiallyTimed bound := by
  obtain ⟨closing,hclosing,hclosingExit⟩ := extractionForwardClosingLoopTemplate_resources tm bound
  obtain ⟨first,hfirstExit⟩ := extractionTraversalLift_budget (extractionForwardClosingLoopTemplate tm) bound ⟨closing,hclosingExit⟩
  have hfirst := extractionTraversalLift_polynomial (extractionForwardClosingLoopTemplate tm) bound hclosing
  obtain ⟨⟨second,hsecondExit⟩,hsecond⟩ := extractionDescendingPassHandoffTemplate_resources first
  obtain ⟨third,hthird,hthirdExit⟩ := extractionForwardPrefixLoopTemplate_resources tm e stride second
  refine ⟨⟨third,?_⟩,?_⟩
  · intro n cs hb q
    exact hthirdExit n _ (hsecondExit n _ (hfirstExit n cs hb)) q
  · apply sequenceProgramTemplate_polynomial _ _ bound first
    · exact hfirst
    · intro n cs hb hr
      exact hfirstExit n cs hb
    · exact sequenceProgramTemplate_polynomial _ _ first second hsecond
        (fun n cs hb _ => hsecondExit n cs hb) hthird

end ShiReversibleGenerator
