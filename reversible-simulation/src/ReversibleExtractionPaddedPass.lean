import ReversibleExtractionForwardPass
import ReversibleExtractionInversePass
import ReversibleExtractionPaddedLiftBudget

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Lift the actual whole formula pass while retaining both original and padded roots. -/
noncomputable def extractionPaddedPassTemplate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : CounterProgramTemplate ExtractionPaddedRegister :=
  extractionPaddedLift (if backward then extractionInversePassTemplate tm e stride else extractionForwardPassTemplate tm e stride)

theorem extractionPaddedPassTemplate_embeds (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionPaddedPassTemplate tm e stride backward).Embeds := by
  cases backward
  · exact extractionPaddedLift_embeds _
  · exact extractionPaddedLift_embeds _

theorem extractionPaddedPassTemplate_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionPaddedPassTemplate tm e stride backward).Runs := by
  cases backward
  · exact extractionPaddedLift_run _ (extractionForwardPassTemplate_embeds tm e stride) (extractionForwardPassTemplate_run tm e stride)
  · exact extractionPaddedLift_run _ (extractionInversePassTemplate_embeds tm e stride) (extractionInversePassTemplate_run tm e stride)

theorem extractionPaddedPassTemplate_ready (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat) (hb : cs 17=0) :
    (extractionPaddedPassTemplate tm e stride backward).ready cs := by
  cases backward
  · exact extractionForwardPassTemplate_ready tm e stride _ hb
  · exact extractionInversePassTemplate_ready tm e stride _ hb

theorem extractionPaddedPassTemplate_roots (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat)
    (q : ExtractionPaddedRegister) (hq : 24 ≤ q.val) :
    (extractionPaddedPassTemplate tm e stride backward).counters cs q=cs q :=
  extractionPaddedLift_outside _ cs q hq

theorem extractionPaddedPassTemplate_resources (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (extractionPaddedPassTemplate tm e stride backward).CounterBound bound ∧
      (extractionPaddedPassTemplate tm e stride backward).PolynomiallyTimed bound := by
  have h : (if backward then extractionInversePassTemplate tm e stride else extractionForwardPassTemplate tm e stride).CounterBound bound ∧
      (if backward then extractionInversePassTemplate tm e stride else extractionForwardPassTemplate tm e stride).PolynomiallyTimed bound := by
    cases backward
    · exact extractionForwardPassTemplate_resources tm e stride bound
    · exact extractionInversePassTemplate_resources tm e stride bound
  exact ⟨extractionPaddedLift_budget _ bound h.1,extractionPaddedLift_polynomial _ bound h.2⟩

end ShiReversibleGenerator
