import ReversibleExtractionInversePass
import ReversibleExtractionClosingStepScratchMetadata

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionInverseClosingStepTemplate_scratch (tm : Turing.FinTM2) (cs : ExtractionTermRegister → Nat) :
    (extractionInverseClosingStepTemplate tm).counters cs 7=0 := by
  change extractionInverseClosingAdvanceTemplate.counters
    ((extractionBoundClosingPrinterTemplate tm true).counters ((extractionInverseClosingRetreatTemplate tm).counters cs)) 7=0
  rw [extractionInverseClosingAdvanceTemplate_counters]
  simp only [Function.update_of_ne (by decide : (7 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (7 : ExtractionTermRegister) ≠ 20)]
  exact (extractionBoundClosingPrinterTemplate_cache tm true _).2.2.2.1

theorem extractionInverseClosingLoopTemplate_scratch (tm : Turing.FinTM2) (cs : ExtractionTraversalRegister → Nat)
    (h7 : cs 7=0) : (extractionInverseClosingLoopTemplate tm).counters cs 7=0 := by
  have hs : ∀ t : ExtractionTraversalRegister → Nat,
      (extractionInverseClosingTraversalStepTemplate tm).counters t 7=0 := by
    intro t
    have h := extractionTraversalLift_pull (extractionInverseClosingStepTemplate tm) t 7
    rw [extractionInverseClosingStepTemplate_scratch] at h
    exact h
  have h : ∀ k (t : ExtractionTraversalRegister → Nat),t 7=0 →
      descendingTemplateCounters (extractionInverseClosingTraversalStepTemplate tm) 22 k t 7=0 := by
    intro k
    induction k with
    | zero => intro t ht; exact ht
    | succ k ih => intro t ht; exact ih _ (hs _)
  change Function.update (descendingTemplateCounters _ 22 (cs 22) cs) 22 0 7=0
  rw [Function.update_of_ne (by decide : (7 : ExtractionTraversalRegister) ≠ 22)]
  exact h _ cs h7

/-- Actual inverse passes leave the emitter scratch empty and retain the zero output buffer. -/
theorem extractionInversePassTemplate_scratch (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionTraversalRegister → Nat) :
    (extractionInversePassTemplate tm e stride).counters cs 7=0 ∧
      (extractionInversePassTemplate tm e stride).counters cs 17=cs 17 := by
  let t := (extractionInversePrefixLoopTemplate tm e stride).counters cs
  let u := extractionInverseClosingHandoffTemplate.counters t
  have hu7 : u 7=0 := by simp [u,extractionInverseClosingHandoffTemplate_counters,cleanupCounters_apply]
  have ht17 : t 17=cs 17 := descendingProgramTemplate_point_frame
    (extractionInversePrefixTraversalStepTemplate tm e stride) 22 17 (by decide)
      (extractionInversePrefixTraversalStepTemplate_buffer tm e stride) cs
  have hu17 : u 17=t 17 := by simp [u,extractionInverseClosingHandoffTemplate_counters,cleanupCounters_apply]
  have hc17 := descendingProgramTemplate_point_frame (extractionInverseClosingTraversalStepTemplate tm) 22 17
    (by decide) (extractionInverseClosingTraversalStepTemplate_buffer tm) u
  exact ⟨extractionInverseClosingLoopTemplate_scratch tm u hu7,hc17.trans (hu17.trans ht17)⟩

end ShiReversibleGenerator
