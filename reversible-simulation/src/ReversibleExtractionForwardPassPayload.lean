import ReversibleExtractionForwardPass
import ReversibleExtractionForwardClosingCertificate
import ReversibleExtractionForwardClosingFinalCoordinates
import ReversibleExtractionForwardClosingSourceFrames
import ReversibleExtractionNaturalFormulaAgreement
import ReversibleExtractionDisjoinPayloadPasses

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The two actual forward passes emit exactly the original extraction compiler payload. -/
theorem extractionForwardPassTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (hell : cs 2=0) (hcount : cs 9=cs 0+1)
    (hend : cs 20=cs 18+((extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1)).map (fun p => p.size+4)).sum) :
    (extractionForwardPassTemplate tm e stride).bytes cs=
      (((disjoin (extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1))).rawCompile
        (fun bit => cs 11+stride*naturalConfigurationAddress tm (cs 0) bit) (cs 18)).map
          (rawAssignmentPayload false)).flatten := by
  let small := fun r => cs (extractionTermToTraversalRegister r)
  let t := (extractionTraversalLift (extractionForwardClosingLoopTemplate tm)).counters cs
  let u := extractionDescendingPassHandoffTemplate.counters t
  let terms := extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1)
  have hlimit : small 2+small 9 ≤ small 0+1 := by change cs 2+cs 9 ≤ cs 0+1; rw [hell,hcount]; omega
  have ht0 : t 0=cs 0 := extractionForwardClosingLift_source_frame tm cs 0 (by simp)
  have ht1 : t 1=cs 1 := extractionForwardClosingLift_source_frame tm cs 1 (by simp)
  have ht11 : t 11=cs 11 := extractionForwardClosingLift_source_frame tm cs 11 (by simp)
  have hc := extractionForwardClosingLoopTemplate_coordinates tm e small hlimit
  have ht18 : t 18=cs 18+(terms.map (fun p => p.size+1)).sum := by
    have h := extractionTraversalLift_pull (extractionForwardClosingLoopTemplate tm) cs 18
    rw [hc.2] at h
    change t 18=cs 18+((extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 9)).map (fun p => p.size+1)).sum at h
    simpa only [hell,hcount] using h
  have hu0 : u 0=cs 0 := by simp [u,extractionDescendingPassHandoffTemplate_counters,cleanupCounters_apply,ht0]
  have hu1 : u 1=cs 1 := by simp [u,extractionDescendingPassHandoffTemplate_counters,cleanupCounters_apply,ht1]
  have hu11 : u 11=cs 11 := by simp [u,extractionDescendingPassHandoffTemplate_counters,cleanupCounters_apply,ht11]
  have hu2 : u 2=cs 0 := by simp [u,extractionDescendingPassHandoffTemplate_counters,ht0]
  have hu22 : u 22=cs 0+1 := by simp [u,extractionDescendingPassHandoffTemplate_counters,ht0]
  have hu18 : u 18=cs 18+(terms.map (fun p => p.size+1)).sum := by
    simp [u,extractionDescendingPassHandoffTemplate_counters,cleanupCounters_apply,ht18]
  have hp := extractionForwardPrefixLoop_payload tm e stride (u 22) u (cs 18)
    (by rw [hu22,hu0]) (by rw [hu2,hu22]; omega)
    (by rw [hu18,hu0,hu1,hu22])
  change (extractionForwardPrefixLoopTemplate tm e stride).bytes u=_ at hp
  have hp' : (extractionForwardPrefixLoopTemplate tm e stride).bytes u=
      ((disjoinTermPrefix (fun bit => cs 11+stride*naturalConfigurationAddress tm (cs 0) bit)
        (cs 18) terms).map (rawAssignmentPayload false)).flatten := hp.trans (by rw [hu0,hu1,hu11,hu22])
  have hs := extractionForwardClosingLoopTemplate_payload tm e small hlimit
    (by change cs 20=cs 18+((extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 9)).map (fun p => p.size+4)).sum; simpa only [hell,hcount] using hend)
  have hs' : (extractionTraversalLift (extractionForwardClosingLoopTemplate tm)).bytes cs=
      ((disjoinClosingSuffix (cs 18) (cs 18+(terms.map (fun p => p.size+4)).sum) terms).map
        (rawAssignmentPayload false)).flatten := hs.trans (by
      change ((disjoinClosingSuffix (cs 18) (cs 20) (extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 9))).map _).flatten=_
      rw [hell,hcount,hend])
  change (extractionForwardPrefixLoopTemplate tm e stride).bytes u ++
    extractionDescendingPassHandoffTemplate.bytes t ++
    (extractionTraversalLift (extractionForwardClosingLoopTemplate tm)).bytes cs=_
  rw [hp',extractionDescendingPassHandoffTemplate_bytes,List.append_nil,hs']
  exact (disjoin_forward_payload_passes terms _ (cs 18)).symm

end ShiReversibleGenerator
