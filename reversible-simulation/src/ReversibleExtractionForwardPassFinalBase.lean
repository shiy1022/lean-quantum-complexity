import ReversibleExtractionForwardPassPayload
import ReversibleExtractionForwardPrefixFinalBase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Whole forward formula emission restores the original workspace base for the next padded output slot. -/
theorem extractionForwardPassTemplate_base (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (hell : cs 2=0) (hcount : cs 9=cs 0+1) :
    (extractionForwardPassTemplate tm e stride).counters cs 18=cs 18 := by
  let small := fun r => cs (extractionTermToTraversalRegister r)
  let t := (extractionTraversalLift (extractionForwardClosingLoopTemplate tm)).counters cs
  let u := extractionDescendingPassHandoffTemplate.counters t
  let terms := extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1)
  have hlimit : small 2+small 9 ≤ small 0+1 := by change cs 2+cs 9 ≤ cs 0+1; rw [hell,hcount]; omega
  have ht0 : t 0=cs 0 := extractionForwardClosingLift_source_frame tm cs 0 (by simp)
  have ht1 : t 1=cs 1 := extractionForwardClosingLift_source_frame tm cs 1 (by simp)
  have hc := extractionForwardClosingLoopTemplate_coordinates tm e small hlimit
  have ht18 : t 18=cs 18+(terms.map (fun p => p.size+1)).sum := by
    have h := extractionTraversalLift_pull (extractionForwardClosingLoopTemplate tm) cs 18
    rw [hc.2] at h
    change t 18=cs 18+((extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 9)).map (fun p => p.size+1)).sum at h
    simpa only [hell,hcount] using h
  have hu0 : u 0=cs 0 := by simp [u,extractionDescendingPassHandoffTemplate_counters,cleanupCounters_apply,ht0]
  have hu1 : u 1=cs 1 := by simp [u,extractionDescendingPassHandoffTemplate_counters,cleanupCounters_apply,ht1]
  have hu2 : u 2=cs 0 := by simp [u,extractionDescendingPassHandoffTemplate_counters,ht0]
  have hu22 : u 22=cs 0+1 := by simp [u,extractionDescendingPassHandoffTemplate_counters,ht0]
  have hu18 : u 18=cs 18+(terms.map (fun p => p.size+1)).sum := by
    simp [u,extractionDescendingPassHandoffTemplate_counters,cleanupCounters_apply,ht18]
  change (extractionForwardPrefixLoopTemplate tm e stride).counters u 18=cs 18
  exact extractionForwardPrefixLoopTemplate_base tm e stride u (cs 18)
    (by rw [hu22,hu0]) (by rw [hu2,hu22]; omega)
    (by rw [hu18,hu0,hu1,hu22])

end ShiReversibleGenerator
