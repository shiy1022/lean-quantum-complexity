import ReversibleExtractionPrefixSchemaCountBound
import ReversibleExtractionInversePrefixStepReady

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Finite inverse-body schemas bound actual counts without a semantic interval assumption. -/
theorem extractionInversePrefixStepTemplate_schema_count_bound (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) :
    (extractionInversePrefixStepTemplate tm e stride).counters cs 16 ≤
      cs 16+(37*extractionTermSchemaBudget tm e+2) := by
  let t := (extractionTermSizeProgramTemplate tm).counters cs
  let u := (extractionBoundTermPrinterTemplate tm e stride true).counters t
  let v := (extractionTermNegationPrinterTemplate true).counters u
  have ht16 : t 16=cs 16 := by simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have hc : u 16 ≤ t 16+37*extractionTermSchemaBudget tm e :=
    extractionBoundTermPrinterTemplate_schema_count_bound tm e stride true t
  change extractionPrefixAdvanceTemplate.counters v 16 ≤ _
  simp only [extractionPrefixAdvanceTemplate_counters,
    Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 18),
    Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 8)]
  change (extractionTermNegationPrinterTemplate true).counters u 16 ≤ _
  rw [extractionTermNegationPrinterTemplate_count,ht16] at *
  omega

end ShiReversibleGenerator
