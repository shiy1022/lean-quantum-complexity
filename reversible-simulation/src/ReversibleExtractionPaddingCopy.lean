import ReversibleCountedCopyProgramTemplate
import ReversibleExtractionTraversalRegisterInjection
import ReversibleProgramTemplateListBudget
import ReversibleFixedFormulaPrinter

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- The padded extraction root is a real counted CNOT from the original result, in either circuit direction. -/
noncomputable def extractionPaddingCopyTemplate : CounterProgramTemplate ExtractionTraversalRegister :=
  countedCopyProgramTemplate 23 21 16 17 7

theorem extractionPaddingCopyTemplate_embeds : extractionPaddingCopyTemplate.Embeds :=
  countedCopyProgramTemplate_embeds _ _ _ _ _

theorem extractionPaddingCopyTemplate_run : extractionPaddingCopyTemplate.Runs :=
  countedCopyProgramTemplate_run _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem extractionPaddingCopyTemplate_ready (cs : ExtractionTraversalRegister → Nat)
    (h17 : cs 17=0) (h7 : cs 7=0) : extractionPaddingCopyTemplate.ready cs := ⟨h17,h7⟩

theorem extractionPaddingCopyTemplate_counters (cs : ExtractionTraversalRegister → Nat) :
    extractionPaddingCopyTemplate.counters cs=Function.update cs 16 (cs 16+1) := rfl

theorem extractionPaddingCopyTemplate_payload (cs : ExtractionTraversalRegister → Nat) (backward : Bool) :
    extractionPaddingCopyTemplate.bytes cs=rawAssignmentPayload backward (.copy (cs 23) (cs 21)) := by
  exact assignmentAtoms_payload .copy (23 : ExtractionTraversalRegister) 23 21 cs

theorem extractionPaddingCopyTemplate_resources (bound : Polynomial Nat) :
    extractionPaddingCopyTemplate.CounterBound bound ∧ extractionPaddingCopyTemplate.PolynomiallyTimed bound := by
  refine ⟨⟨bound+Polynomial.C 1,?_⟩,countedCopyProgramTemplate_polynomial _ _ _ _ _ bound⟩
  intro n cs hb q
  have hc := hb 16
  have hq := hb q
  simp only [extractionPaddingCopyTemplate_counters,Function.update_apply,Polynomial.eval_add,Polynomial.eval_C]
  split_ifs <;> omega

end ShiReversibleGenerator
