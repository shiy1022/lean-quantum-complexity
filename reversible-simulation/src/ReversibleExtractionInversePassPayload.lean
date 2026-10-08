import ReversibleExtractionInversePass
import ReversibleExtractionInversePrefixFinalCoordinates
import ReversibleExtractionInversePrefixSourceFrames
import ReversibleExtractionNaturalFormulaAgreement
import ReversibleExtractionDisjoinPayloadPasses

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Both actual inverse passes assemble the exact original disjoin compiler payload in reverse. -/
theorem extractionInversePassTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (hell : cs 2=0) (hcount : cs 22=cs 0+1) :
    (extractionInversePassTemplate tm e stride).bytes cs=
      ((((disjoin (extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1))).rawCompile
        (fun bit => cs 11+stride*naturalConfigurationAddress tm (cs 0) bit) (cs 18)).reverse).map
          (rawAssignmentPayload true)).flatten := by
  let t := (extractionInversePrefixLoopTemplate tm e stride).counters cs
  let u := extractionInverseClosingHandoffTemplate.counters t
  let terms := extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 0+1)
  have hlimit : cs 2+cs 22 ≤ cs 0+1 := by rw [hell,hcount]; omega
  have ht0 : t 0=cs 0 := extractionInversePrefixLoopTemplate_source_frame tm e stride cs 0 (by simp)
  have ht1 : t 1=cs 1 := extractionInversePrefixLoopTemplate_source_frame tm e stride cs 1 (by simp)
  have hc := extractionInversePrefixLoopTemplate_coordinates tm e stride cs hlimit
  have ht18 : t 18=cs 18+(terms.map (fun p => p.size+1)).sum := by
    have h := hc.2
    rw [hell,hcount] at h
    exact h
  have hu0 : u 0=cs 0 := by simp [u,extractionInverseClosingHandoffTemplate_counters,cleanupCounters_apply,ht0]
  have hu1 : u 1=cs 1 := by simp [u,extractionInverseClosingHandoffTemplate_counters,cleanupCounters_apply,ht1]
  have hu2 : u 2=cs 0 := by simp [u,extractionInverseClosingHandoffTemplate_counters,ht0]
  have hu22 : u 22=cs 0+1 := by simp [u,extractionInverseClosingHandoffTemplate_counters,ht0]
  have hu18 : u 18=cs 18+(terms.map (fun p => p.size+1)).sum := by
    simp [u,extractionInverseClosingHandoffTemplate_counters,cleanupCounters_apply,ht18]
  have hu20 : u 20=cs 18+(terms.map (fun p => p.size+1)).sum+3 := by
    simp [u,extractionInverseClosingHandoffTemplate_counters,ht18]
  have he : u 20+3*u 22-3=cs 18+(terms.map (fun p => p.size+4)).sum := by
    rw [hu20,hu22]
    have hl : terms.length=cs 0+1 := extractionNaturalTermRange_length tm e (cs 0) (cs 1) 0 _
    have hx := extractionClosingEndpoint_sum terms
    rw [hl] at hx
    omega
  have hp := extractionInversePrefixLoop_payload tm e stride (cs 22) cs hlimit
  change (extractionInversePrefixLoopTemplate tm e stride).bytes cs=_ at hp
  have hp' : (extractionInversePrefixLoopTemplate tm e stride).bytes cs=
      (((disjoinTermPrefix (fun bit => cs 11+stride*naturalConfigurationAddress tm (cs 0) bit)
        (cs 18) terms).reverse).map (rawAssignmentPayload true)).flatten :=
    hp.trans (by rw [hell,hcount])
  have hs := extractionInverseClosingLoop_payload tm e (u 22) 0 (cs 18) u
    (by rw [hu2,hu22]; omega) (by rw [hu22,hu0]; omega)
    (by rw [hu18,hu0,hu1,hu22]) (by rw [hu20]; omega)
  change (extractionInverseClosingLoopTemplate tm).bytes u=_ at hs
  have hs' : (extractionInverseClosingLoopTemplate tm).bytes u=
      (((disjoinClosingSuffix (cs 18) (cs 18+(terms.map (fun p => p.size+4)).sum) terms).reverse).map
        (rawAssignmentPayload true)).flatten := hs.trans (by rw [he,hu0,hu1,hu22])
  change (extractionInverseClosingLoopTemplate tm).bytes u ++
    extractionInverseClosingHandoffTemplate.bytes t ++ (extractionInversePrefixLoopTemplate tm e stride).bytes cs=_
  rw [hs',extractionInverseClosingHandoffTemplate_bytes,List.append_nil,hp']
  exact (disjoin_inverse_payload_passes terms _ (cs 18)).symm

end ShiReversibleGenerator
