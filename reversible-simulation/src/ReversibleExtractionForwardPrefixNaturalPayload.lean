import ReversibleExtractionForwardPrefixStepPayload
import ReversibleExtractionNaturalTermRange

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

theorem extractionForwardPrefixStepTemplate_natural_payload (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat)
    (hell : cs 2 ≤ cs 0) :
    let p := extractionNaturalTerm tm e (cs 0) (cs 2) (cs 1)
    let base := cs 18-(p.size+1)
    let inputs := fun bit => cs 11+stride*naturalConfigurationAddress tm (cs 0) bit
    (extractionForwardPrefixStepTemplate tm e stride).bytes cs=
      ((p.rawCompile inputs base ++ [RawAssignment.neg (p.result base) (base+p.size)]).map
        (rawAssignmentPayload false)).flatten := by
  have h := extractionForwardPrefixStepTemplate_payload tm e stride cs hell
  simpa [extractionNaturalTerm,Formula.rename_size,Formula.rename_rawCompile,
    Formula.result,Function.comp_def] using h

end ShiReversibleGenerator
