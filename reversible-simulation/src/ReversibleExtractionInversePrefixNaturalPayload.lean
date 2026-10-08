import ReversibleExtractionInversePrefixStepPayload
import ReversibleExtractionNaturalTermRange

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem extractionInversePrefixStepTemplate_natural_payload (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat)
    (hell : cs 2 ≤ cs 0) :
    let p := extractionNaturalTerm tm e (cs 0) (cs 2) (cs 1)
    let inputs := fun bit => cs 11+stride*naturalConfigurationAddress tm (cs 0) bit
    (extractionInversePrefixStepTemplate tm e stride).bytes cs=
      (((p.rawCompile inputs (cs 18) ++ [RawAssignment.neg (p.result (cs 18)) (cs 18+p.size)]).reverse).map
        (rawAssignmentPayload true)).flatten := by
  have h := extractionInversePrefixStepTemplate_payload tm e stride cs hell
  simpa [extractionNaturalTerm,Formula.rename_size,Formula.rename_rawCompile,
    Formula.result,Function.comp_def] using h

end ShiReversibleGenerator
