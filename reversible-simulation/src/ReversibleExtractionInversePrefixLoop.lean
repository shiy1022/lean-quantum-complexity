import ReversibleExtractionInversePrefixStepReady
import ReversibleDescendingProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

noncomputable def extractionInversePrefixTraversalStepTemplate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :=
  extractionTraversalLift (extractionInversePrefixStepTemplate tm e stride)

/-- Ascending inverse traversal uses the disjoint outer counter22. -/
noncomputable def extractionInversePrefixLoopTemplate (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :=
  descendingProgramTemplate (extractionInversePrefixTraversalStepTemplate tm e stride) 22

theorem extractionInversePrefixLoopTemplate_embeds (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :
    (extractionInversePrefixLoopTemplate tm e stride).Embeds :=
  descendingProgramTemplate_embeds _ _ (extractionTraversalLift_embeds _)

theorem extractionInversePrefixLoopTemplate_run (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) :
    (extractionInversePrefixLoopTemplate tm e stride).Runs :=
  descendingProgramTemplate_run _ _ (extractionTraversalLift_embeds _)
    (extractionTraversalLift_run _ (extractionInversePrefixStepTemplate_embeds tm e stride)
      (extractionInversePrefixStepTemplate_run tm e stride))

theorem extractionInversePrefixStepTemplate_buffer (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTermRegister → Nat) :
    (extractionInversePrefixStepTemplate tm e stride).counters cs 17=cs 17 := by
  let t := (extractionTermSizeProgramTemplate tm).counters cs
  let u := (extractionBoundTermPrinterTemplate tm e stride true).counters t
  let v := (extractionTermNegationPrinterTemplate true).counters u
  have ht : t 17=cs 17 := by simp [t,extractionTermSizeProgramTemplate_counters,cleanupCounters_apply]
  have hu : u 17=t 17 := extractionBoundTermPrinterTemplate_frame tm e stride true t 17
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hv : v 17=u 17 := extractionTermNegationPrinterTemplate_frame true u 17
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  change extractionPrefixAdvanceTemplate.counters v 17=cs 17
  simpa only [extractionPrefixAdvanceTemplate_counters,
    Function.update_of_ne (by decide : (17 : ExtractionTermRegister) ≠ 2),
    Function.update_of_ne (by decide : (17 : ExtractionTermRegister) ≠ 18),
    Function.update_of_ne (by decide : (17 : ExtractionTermRegister) ≠ 8)] using hv.trans (hu.trans ht)

theorem extractionInversePrefixTraversalStepTemplate_buffer (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat) :
    (extractionInversePrefixTraversalStepTemplate tm e stride).counters cs 17=cs 17 := by
  have h := extractionTraversalLift_pull (extractionInversePrefixStepTemplate tm e stride) cs 17
  rw [extractionInversePrefixStepTemplate_buffer] at h
  exact h

theorem extractionInversePrefixLoopTemplate_ready (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (h17 : cs 17=0) :
    (extractionInversePrefixLoopTemplate tm e stride).ready cs := by
  suffices h : ∀ k (t : ExtractionTraversalRegister → Nat),t 17=0 →
      descendingTemplateReady (extractionInversePrefixTraversalStepTemplate tm e stride) 22 k t by
    exact h _ _ h17
  intro k
  induction k with
  | zero => intro t ht; trivial
  | succ k ih =>
    intro t ht
    let next := Function.update t (22 : ExtractionTraversalRegister) k
    have hn : next 17=0 := by simpa [next] using ht
    refine ⟨?_,?_,ih _ ?_⟩
    · exact extractionInversePrefixStepTemplate_ready tm e stride
        (fun r => next (extractionTermToTraversalRegister r)) hn
    · exact (extractionTraversalLift_outside (extractionInversePrefixStepTemplate tm e stride)
        next 22 (by decide)).trans (Function.update_self _ _ _)
    · exact (extractionInversePrefixTraversalStepTemplate_buffer tm e stride next).trans hn

end ShiReversibleGenerator
