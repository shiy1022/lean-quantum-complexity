import ReversibleExtractionInverseClosingTraversalMetadata
import ReversibleExtractionNaturalTermRangeSnoc

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The actual inverse closing pass retreats exactly to the original formula base. -/
theorem extractionInverseClosing_descending_base (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (k : Nat) (cs : ExtractionTraversalRegister → Nat) (base : Nat)
    (hk : k ≤ cs 0+1) (hell : cs 2=k-1)
    (hend : cs 18=base+((extractionNaturalTermRange tm e (cs 0) (cs 1) 0 k).map (fun p => p.size+1)).sum) :
    descendingTemplateCounters (extractionInverseClosingTraversalStepTemplate tm) 22 k cs 18=base := by
  induction k generalizing cs with
  | zero => simpa only [descendingTemplateCounters,extractionNaturalTermRange,List.map_nil,List.sum_nil,Nat.add_zero] using hend
  | succ k ih =>
    let next := Function.update cs (22 : ExtractionTraversalRegister) k
    let after := (extractionInverseClosingTraversalStepTemplate tm).counters next
    have hn0 : next 0=cs 0 := by simp [next]
    have hn1 : next 1=cs 1 := by simp [next]
    have hn2 : next 2=k := by simpa [next] using hell
    have hn18 : next 18=cs 18 := by simp [next]
    have hm := extractionInverseClosingTraversalStepTemplate_metadata tm next
    dsimp only at hm
    rw [hn0,hn1,hn2,hn18] at hm
    have h0 : after 0=cs 0 := hm.1
    have h1 : after 1=cs 1 := hm.2.1
    have h2 : after 2=k-1 := hm.2.2.1
    have hp := extractionNaturalTerm_size tm e (cs 0) k (cs 1) (by omega)
    have he : cs 18=base+
        (((extractionNaturalTermRange tm e (cs 0) (cs 1) 0 k).map (fun p => p.size+1)).sum+
          ((extractionNaturalTerm tm e (cs 0) k (cs 1)).size+1)) := by
      rw [extractionNaturalTermRange_snoc] at hend
      simpa only [Nat.zero_add,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton] using hend
    have h18 : after 18=base+((extractionNaturalTermRange tm e (cs 0) (cs 1) 0 k).map (fun p => p.size+1)).sum := by
      have h := hm.2.2.2.1
      rw [←hp] at h
      change after 18=cs 18-((extractionNaturalTerm tm e (cs 0) k (cs 1)).size+4-3) at h
      omega
    exact ih after (by rw [h0]; omega) h2 (by rw [h0,h1]; exact h18)

theorem extractionInverseClosingLoopTemplate_base (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (cs : ExtractionTraversalRegister → Nat) (base : Nat)
    (hk : cs 22 ≤ cs 0+1) (hell : cs 2=cs 22-1)
    (hend : cs 18=base+((extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 22)).map (fun p => p.size+1)).sum) :
    (extractionInverseClosingLoopTemplate tm).counters cs 18=base := by
  change Function.update (descendingTemplateCounters _ 22 (cs 22) cs) 22 0 18=base
  rw [Function.update_of_ne (by decide : (18 : ExtractionTraversalRegister) ≠ 22)]
  exact extractionInverseClosing_descending_base tm e (cs 22) cs base hk hell hend

end ShiReversibleGenerator
