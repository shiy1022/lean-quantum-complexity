import ReversibleExtractionSizeCertificate
import ReversibleExtractionTermSizeProgram
import ReversibleExtractionPaddedRegisterInjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- The original runtime whole-formula size pass uses register12 without touching the saved padded roots. -/
def extractionSizeToPaddedRegister (r : ExtractionSizeRegister) : ExtractionPaddedRegister :=
  extractionTraversalToPaddedRegister (extractionTermToTraversalRegister (extractionSizeToTermRegister r))

theorem extractionSizeToPaddedRegister_injective : Function.Injective extractionSizeToPaddedRegister :=
  extractionTraversalToPaddedRegister_injective.comp (extractionTermToTraversalRegister_injective.comp extractionSizeToTermRegister_injective)

noncomputable def extractionWholeSizeProgramTemplate (tm : Turing.FinTM2) : CounterProgramTemplate ExtractionPaddedRegister :=
  injectProgramTemplate (extractionSizeMasterTemplate tm) extractionSizeToPaddedRegister 2

theorem extractionWholeSizeProgramTemplate_embeds (tm : Turing.FinTM2) :
    (extractionWholeSizeProgramTemplate tm).Embeds := injectProgramTemplate_embeds _ _ _

theorem extractionWholeSizeProgramTemplate_run (tm : Turing.FinTM2) :
    (extractionWholeSizeProgramTemplate tm).Runs :=
  injectProgramTemplate_run _ _ extractionSizeToPaddedRegister_injective _
    (extractionSizeMasterTemplate_embeds tm) (extractionSizeMasterTemplate_run tm)

theorem extractionWholeSizeProgramTemplate_ready (tm : Turing.FinTM2) (cs : ExtractionPaddedRegister → Nat) :
    (extractionWholeSizeProgramTemplate tm).ready cs := extractionSizeMasterTemplate_ready tm _

theorem extractionWholeSizeProgramTemplate_value (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (cs : ExtractionPaddedRegister → Nat) :
    (extractionWholeSizeProgramTemplate tm).counters cs 12=(extractionFormula tm e (cs 0) (cs 1)).size := by
  change injectedTemplateCounters extractionSizeToPaddedRegister cs _ (extractionSizeToPaddedRegister 4)=_
  rw [injectedTemplateCounters_pull _ extractionSizeToPaddedRegister_injective]
  exact (extractionSizeMasterTemplate_result tm e _).1

theorem extractionWholeSizeProgramTemplate_bytes (tm : Turing.FinTM2) (cs : ExtractionPaddedRegister → Nat) :
    (extractionWholeSizeProgramTemplate tm).bytes cs=[] := extractionSizeMasterTemplate_bytes tm _

theorem extractionWholeSizeProgramTemplate_polynomial (tm : Turing.FinTM2) (bound : Polynomial Nat) :
    (extractionWholeSizeProgramTemplate tm).PolynomiallyTimed bound :=
  injectProgramTemplate_polynomial _ _ _ _ (extractionSizeMasterTemplate_polynomial tm bound)

theorem extractionWholeSizeProgramTemplate_outside (tm : Turing.FinTM2) (cs : ExtractionPaddedRegister → Nat)
    (q : ExtractionPaddedRegister) (hq : 13 ≤ q.val) :
    (extractionWholeSizeProgramTemplate tm).counters cs q=cs q := by
  apply injectedTemplateCounters_outside
  intro r hr
  have hv := congrArg Fin.val hr
  simp only [extractionSizeToPaddedRegister,extractionTraversalToPaddedRegister,
    extractionTermToTraversalRegister,extractionSizeToTermRegister] at hv
  have hl := r.isLt
  split_ifs at hv <;> omega

end ShiReversibleGenerator
