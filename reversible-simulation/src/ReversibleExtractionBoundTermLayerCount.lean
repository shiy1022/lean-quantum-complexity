import ReversibleExtractionBoundTermPrinter
import ReversibleExtractionDispatchLayerCount
import ReversibleInitializationExactLayers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Schema selection preserves the exact elementary count of the original selected term. -/
theorem extractionTermSchema_layers_agreement (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (capacity ell j : Nat) (hell : ell ≤ capacity) :
    formulaElementaryLayers (extractionTermSchema tm e (decide (ell=0)) (decide (capacity ≤ ell))
      (extractionRuntimeValueKind ell j))=
    formulaElementaryLayers (Formula.conj (lengthFlag (extractionEmpty tm capacity) ell)
      (outputValue (extractionPayload tm e capacity) ell j)) := by
  have h := congrArg formulaElementaryLayers (extractionTermSchema_agreement tm e capacity ell j hell)
  simpa only [formulaElementaryLayers_rename] using h

/-- Setup preserves the counter; the actual selected term increments it by the original compiler's exact count. -/
theorem extractionBoundTermPrinterTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionTermRegister → Nat) (hell : cs 2 ≤ cs 0) :
    (extractionBoundTermPrinterTemplate tm e stride backward).counters cs 16=
      cs 16+formulaElementaryLayers (Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
        (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))) := by
  have frame : ∀ q ∈ ([0,1,2,16] : List ExtractionTermRegister),
      (extractionInputSetupTemplate tm stride).counters cs q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq | hq | hq | hq
    all_goals subst q
    all_goals exact extractionInputSetupTemplate_frame tm stride cs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  change (extractionTermDispatchTemplate tm e backward (extractionBoundInputs tm stride)).counters
    ((extractionInputSetupTemplate tm stride).counters cs) 16=_
  rw [extractionTermDispatchTemplate_count]
  simp only [frame 0 (by simp),frame 1 (by simp),frame 2 (by simp),frame 16 (by simp)]
  rw [extractionTermSchema_layers_agreement tm e (cs 0) (cs 2) (cs 1) hell]

end ShiReversibleGenerator
