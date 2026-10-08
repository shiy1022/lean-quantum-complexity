import ReversibleExtractionForwardPass
import ReversibleExtractionForwardPrefixLoopCount
import ReversibleExtractionPassLayerCount

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The assembled forward pass accumulates exactly the elementary layers of the original disjoin formula. -/
theorem extractionForwardPassTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (hcount : cs 9=cs 0+1) :
    (extractionForwardPassTemplate tm e stride).counters cs 16=cs 16+
      formulaElementaryLayers (disjoin (extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1))) := by
  let t := (extractionTraversalLift (extractionForwardClosingLoopTemplate tm)).counters cs
  let u := extractionDescendingPassHandoffTemplate.counters t
  let terms := extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1)
  have ht0 : t 0=cs 0 := extractionForwardClosingLift_source_frame tm cs 0 (by simp)
  have ht1 : t 1=cs 1 := extractionForwardClosingLift_source_frame tm cs 1 (by simp)
  have ht16 : t 16=cs 16+41*(cs 0+1) := by
    have h := extractionTraversalLift_pull (extractionForwardClosingLoopTemplate tm) cs 16
    rw [extractionForwardClosingLoopTemplate_count] at h
    change t 16=cs 16+41*cs 9 at h
    rw [hcount] at h
    exact h
  have hu0 : u 0=cs 0 := by simp [u,extractionDescendingPassHandoffTemplate_counters,cleanupCounters_apply,ht0]
  have hu1 : u 1=cs 1 := by simp [u,extractionDescendingPassHandoffTemplate_counters,cleanupCounters_apply,ht1]
  have hu2 : u 2=cs 0 := by simp [u,extractionDescendingPassHandoffTemplate_counters,ht0]
  have hu16 : u 16=t 16 := by simp [u,extractionDescendingPassHandoffTemplate_counters,cleanupCounters_apply]
  have hu22 : u 22=cs 0+1 := by simp [u,extractionDescendingPassHandoffTemplate_counters,ht0]
  have hp := extractionForwardPrefixLoop_count tm e stride (u 22) u
    (by rw [hu22,hu0]) (by rw [hu2,hu22]; omega)
  change (extractionForwardPrefixLoopTemplate tm e stride).counters u 16=_ at hp
  rw [hu0,hu1,hu16,hu22,ht16] at hp
  have hl : terms.length=cs 0+1 := extractionNaturalTermRange_length tm e (cs 0) (cs 1) 0 _
  have hx := extractionPassLayerCount_split terms
  rw [hl] at hx
  change (extractionForwardPrefixLoopTemplate tm e stride).counters u 16=_
  change (extractionForwardPrefixLoopTemplate tm e stride).counters u 16=
    cs 16+41*(cs 0+1)+(terms.map (fun p => formulaElementaryLayers p+2)).sum at hp
  change (extractionForwardPrefixLoopTemplate tm e stride).counters u 16=cs 16+formulaElementaryLayers (disjoin terms)
  omega

end ShiReversibleGenerator
