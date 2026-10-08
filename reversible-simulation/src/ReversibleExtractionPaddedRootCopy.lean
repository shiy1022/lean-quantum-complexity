import ReversibleCountedCopyProgramTemplate
import ReversibleExtractionPaddedRegisterInjection
import ReversibleProgramTemplateListBudget
import ReversibleFixedFormulaPrinter

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- The padded extraction root is a real counted CNOT from the original result, in either circuit direction. -/
noncomputable def extractionPaddedRootCopyTemplate : CounterProgramTemplate ExtractionPaddedRegister :=
  countedCopyProgramTemplate 24 25 16 17 7

theorem extractionPaddedRootCopyTemplate_embeds : extractionPaddedRootCopyTemplate.Embeds :=
  countedCopyProgramTemplate_embeds _ _ _ _ _

theorem extractionPaddedRootCopyTemplate_run : extractionPaddedRootCopyTemplate.Runs :=
  countedCopyProgramTemplate_run _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem extractionPaddedRootCopyTemplate_ready (cs : ExtractionPaddedRegister → Nat)
    (h17 : cs 17=0) (h7 : cs 7=0) : extractionPaddedRootCopyTemplate.ready cs := ⟨h17,h7⟩

theorem extractionPaddedRootCopyTemplate_counters (cs : ExtractionPaddedRegister → Nat) :
    extractionPaddedRootCopyTemplate.counters cs=Function.update cs 16 (cs 16+1) := rfl

theorem extractionPaddedRootCopyTemplate_payload (cs : ExtractionPaddedRegister → Nat) (backward : Bool) :
    extractionPaddedRootCopyTemplate.bytes cs=rawAssignmentPayload backward (.copy (cs 24) (cs 25)) := by
  exact assignmentAtoms_payload .copy (24 : ExtractionPaddedRegister) 24 25 cs

theorem extractionPaddedRootCopyTemplate_resources (bound : Polynomial Nat) :
    extractionPaddedRootCopyTemplate.CounterBound bound ∧ extractionPaddedRootCopyTemplate.PolynomiallyTimed bound := by
  refine ⟨⟨bound+Polynomial.C 1,?_⟩,countedCopyProgramTemplate_polynomial _ _ _ _ _ bound⟩
  intro n cs hb q
  have hc := hb 16
  have hq := hb q
  simp only [extractionPaddedRootCopyTemplate_counters,Function.update_apply,Polynomial.eval_add,Polynomial.eval_C]
  split_ifs <;> omega

end ShiReversibleGenerator
