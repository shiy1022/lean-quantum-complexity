import ReversibleExtractionInversePassPayload
import ReversibleExtractionInverseClosingFinalBase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Whole inverse formula emission restores the original workspace base after uncomputing its closing suffix. -/
theorem extractionInversePassTemplate_base (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (hell : cs 2=0) (hcount : cs 22=cs 0+1) :
    (extractionInversePassTemplate tm e stride).counters cs 18=cs 18 := by
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
  change (extractionInverseClosingLoopTemplate tm).counters u 18=cs 18
  exact extractionInverseClosingLoopTemplate_base tm e u (cs 18)
    (by rw [hu22,hu0]) (by rw [hu2,hu22]; omega)
    (by rw [hu18,hu0,hu1,hu22])

end ShiReversibleGenerator
