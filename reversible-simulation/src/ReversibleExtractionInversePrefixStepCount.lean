import ReversibleExtractionInversePrefixStepMetadata
import ReversibleExtractionBoundTermLayerCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The ascending inverse body counts exactly the original selected term and its two-layer negation. -/
theorem extractionInversePrefixStepTemplate_count (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) (hell : cs 2 ≤ cs 0) :
    (extractionInversePrefixStepTemplate tm e stride).counters cs 16=
      cs 16+formulaElementaryLayers (Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
        (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1)))+2 := by
  let t := (extractionTermSizeProgramTemplate tm).counters cs
  let u := (extractionBoundTermPrinterTemplate tm e stride true).counters t
  let v := (extractionTermNegationPrinterTemplate true).counters u
  have ht : ∀ q ∈ ([0,1,2,16] : List ExtractionTermRegister),t q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have h0 := ht 0 (by simp)
  have h1 := ht 1 (by simp)
  have h2 := ht 2 (by simp)
  have h16 := ht 16 (by simp)
  change extractionPrefixAdvanceTemplate.counters v 16=_
  rw [extractionPrefixAdvanceTemplate_counters]
  simp only [Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 18),
    Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 8)]
  change (extractionTermNegationPrinterTemplate true).counters u 16=_
  rw [extractionTermNegationPrinterTemplate_count]
  change (extractionBoundTermPrinterTemplate tm e stride true).counters t 16+2=_
  rw [extractionBoundTermPrinterTemplate_count tm e stride true t (by simpa only [h2,h0] using hell),h0,h1,h2,h16]

end ShiReversibleGenerator
