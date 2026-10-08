import ReversibleExtractionForwardPrefixStepPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The real prefix body counts the original selected term and exactly two negation layers. -/
theorem extractionForwardPrefixStepTemplate_count (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) (hell : cs 2 ≤ cs 0) :
    (extractionForwardPrefixStepTemplate tm e stride).counters cs 16=
      cs 16+formulaElementaryLayers (Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
        (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1)))+2 := by
  let t := (extractionForwardTermRetreatTemplate tm).counters cs
  let u := (extractionTermNegationPrinterTemplate false).counters t
  have ht : ∀ q ∈ ([0,1,2,16] : List ExtractionTermRegister),t q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals exact (extractionForwardTermRetreatTemplate_frame tm cs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hu : ∀ q ∈ ([0,1,2] : List ExtractionTermRegister),u q=t q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals exact (extractionTermNegationPrinterTemplate_frame false t _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have h0 := (hu 0 (by simp)).trans (ht 0 (by simp))
  have h1 := (hu 1 (by simp)).trans (ht 1 (by simp))
  have h2 := (hu 2 (by simp)).trans (ht 2 (by simp))
  change (decrementProgramTemplate (2 : ExtractionTermRegister)).counters
    ((extractionBoundTermPrinterTemplate tm e stride false).counters u) 16=_
  simp only [decrementProgramTemplate,Function.update_of_ne (by decide : (16 : ExtractionTermRegister) ≠ 2)]
  rw [extractionBoundTermPrinterTemplate_count tm e stride false u (by simpa only [h2,h0] using hell),h0,h1,h2]
  change (extractionTermNegationPrinterTemplate false).counters t 16+_= _
  rw [extractionTermNegationPrinterTemplate_count,ht 16 (by simp)]
  omega

end ShiReversibleGenerator
