import ReversibleExtractionInversePrefixStepReady
import ReversibleExtractionInversePrefixTraversalMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Printing a negation preserves its freshly bound concrete root and next-wire source counters. -/
theorem extractionTermNegationPrinterTemplate_pointers (backward : Bool) (cs : ExtractionTermRegister → Nat) :
    (extractionTermNegationPrinterTemplate backward).counters cs 19=cs 18+cs 12-5 ∧
    (extractionTermNegationPrinterTemplate backward).counters cs 21=cs 18+cs 12-5+1 := by
  have hf : ∀ q ∈ ([19,21] : List ExtractionTermRegister),
      (extractionTermNegationPrinterTemplate backward).counters cs q=
        extractionTermNegationSetupTemplate.counters cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl
    all_goals exact (fixedNodeCounters_other extractionTermNodeRegisters _ _
      (by decide) (by decide) (by decide) (by decide) _)
  simp [hf 19 (by simp),hf 21 (by simp),extractionTermNegationSetupTemplate_counters]

/-- The inverse body leaves exact freshly bound term pointers, independent of their old values. -/
theorem extractionInversePrefixStepTemplate_pointers (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) :
    let after := (extractionInversePrefixStepTemplate tm e stride).counters cs
    after 19=cs 18+extractionSizeContribution tm (cs 2) (cs 1)-5 ∧
    after 21=cs 18+extractionSizeContribution tm (cs 2) (cs 1)-5+1 := by
  let t := (extractionTermSizeProgramTemplate tm).counters cs
  let u := (extractionBoundTermPrinterTemplate tm e stride true).counters t
  let v := (extractionTermNegationPrinterTemplate true).counters u
  have ht18 : t 18=cs 18 := by simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have ht12 : t 12=extractionSizeContribution tm (cs 2) (cs 1) := extractionTermSizeProgramTemplate_value tm cs
  have hu18 : u 18=t 18 := extractionBoundTermPrinterTemplate_frame tm e stride true t 18
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hu12 : u 12=t 12 := extractionBoundTermPrinterTemplate_frame tm e stride true t 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h18 := hu18.trans ht18
  have h12 := hu12.trans ht12
  have hv := extractionTermNegationPrinterTemplate_pointers true u
  change v 19=u 18+u 12-5 ∧ v 21=u 18+u 12-5+1 at hv
  rw [h18,h12] at hv
  change extractionPrefixAdvanceTemplate.counters v 19=_ ∧ extractionPrefixAdvanceTemplate.counters v 21=_
  simpa only [extractionPrefixAdvanceTemplate_counters,
    Function.update_of_ne (by decide : (19 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (19 : ExtractionTermRegister) ≠ 18),
    Function.update_of_ne (by decide : (19 : ExtractionTermRegister) ≠ 8),
    Function.update_of_ne (by decide : (21 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (21 : ExtractionTermRegister) ≠ 18),
    Function.update_of_ne (by decide : (21 : ExtractionTermRegister) ≠ 8)] using hv

end ShiReversibleGenerator
