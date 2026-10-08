import ReversibleExtractionTermFieldBound
import ReversibleExtractionForwardPrefixStepCount
import ReversibleFormulaLayerCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Finite schemas bound actual term counts for arbitrary runtime metadata, without an interval hypothesis. -/
theorem extractionBoundTermPrinterTemplate_schema_count_bound (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (backward : Bool) (cs : ExtractionTermRegister → Nat) :
    (extractionBoundTermPrinterTemplate tm e stride backward).counters cs 16 ≤
      cs 16+37*extractionTermSchemaBudget tm e := by
  let after := (extractionInputSetupTemplate tm stride).counters cs
  have h16 : after 16=cs 16 := extractionInputSetupTemplate_frame tm stride cs 16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hc := extractionTermDispatchTemplate_count tm e backward (extractionBoundInputs tm stride) after
  have hl := formulaElementaryLayers_bound (extractionTermSchema tm e (decide (after 2=0))
    (decide (after 0 ≤ after 2)) (extractionRuntimeValueKind (after 2) (after 1)))
  have hs := extractionTermSchema_size_bound tm e (decide (after 2=0))
    (decide (after 0 ≤ after 2)) (extractionRuntimeValueKind (after 2) (after 1))
  have hm := Nat.mul_le_mul_left 37 hs
  change (extractionTermDispatchTemplate tm e backward (extractionBoundInputs tm stride)).counters after 16 ≤ _
  rw [hc,h16]
  exact Nat.add_le_add_left (hl.trans hm) _

theorem extractionForwardPrefixStepTemplate_schema_count_bound (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) :
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 16 ≤
      cs 16+(37*extractionTermSchemaBudget tm e+2) := by
  let t := (extractionForwardTermRetreatTemplate tm).counters cs
  let u := (extractionTermNegationPrinterTemplate false).counters t
  have ht : t 16=cs 16 := extractionForwardTermRetreatTemplate_frame tm cs 16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hu : u 16=t 16+2 := extractionTermNegationPrinterTemplate_count false t
  have hc := extractionBoundTermPrinterTemplate_schema_count_bound tm e stride false u
  change (decrementProgramTemplate (2 : ExtractionTermRegister)).counters
    ((extractionBoundTermPrinterTemplate tm e stride false).counters u) 16 ≤ _
  simp only [decrementProgramTemplate,Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 2)]
  rw [ht] at hu
  omega

end ShiReversibleGenerator
