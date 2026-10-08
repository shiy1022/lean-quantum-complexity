import ReversibleExtractionInversePrefixTraversalMetadata
import ReversibleExtractionNaturalTermRange
import ReversibleDescendingTemplatePointFrames

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Actual inverse prefix finishes at the original false-constant base and advances length by the exact term count. -/
theorem extractionInversePrefix_descending_coordinates (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride k : Nat) (cs : ExtractionTraversalRegister → Nat) (hlimit : cs 2+k ≤ cs 0+1) :
    let after := descendingTemplateCounters (extractionInversePrefixTraversalStepTemplate tm e stride) 22 k cs
    after 2=cs 2+k ∧ after 18=cs 18+
      ((extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) k).map (fun p => p.size+1)).sum := by
  induction k generalizing cs with
  | zero => simp [descendingTemplateCounters,extractionNaturalTermRange]
  | succ k ih =>
    let next := Function.update cs (22 : ExtractionTraversalRegister) k
    let after := (extractionInversePrefixTraversalStepTemplate tm e stride).counters next
    have hn0 : next 0=cs 0 := by simp [next]
    have hn1 : next 1=cs 1 := by simp [next]
    have hn2 : next 2=cs 2 := by simp [next]
    have hn18 : next 18=cs 18 := by simp [next]
    have hm := extractionInversePrefixTraversalStepTemplate_metadata tm e stride next
    dsimp only at hm
    rw [hn0,hn1,hn2,hn18] at hm
    have h0 : after 0=cs 0 := hm.1
    have h1 : after 1=cs 1 := hm.2.1
    have h2 : after 2=cs 2+1 := hm.2.2.2.1
    have hp := extractionNaturalTerm_size tm e (cs 0) (cs 2) (cs 1) (by omega)
    have h18 : after 18=cs 18+(extractionNaturalTerm tm e (cs 0) (cs 2) (cs 1)).size+1 := by
      have h := hm.2.2.2.2
      rw [←hp] at h
      change after 18=cs 18+((extractionNaturalTerm tm e (cs 0) (cs 2) (cs 1)).size+4-3) at h
      omega
    have hi := ih after (by rw [h2,h0]; omega)
    dsimp only at hi
    rw [h0,h1,h2,h18] at hi
    simpa only [descendingTemplateCounters,next,extractionNaturalTermRange,List.map_cons,List.sum_cons,
      extractionNaturalTerm,Formula.rename_size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi

theorem extractionInversePrefixLoopTemplate_coordinates (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (hlimit : cs 2+cs 22 ≤ cs 0+1) :
    (extractionInversePrefixLoopTemplate tm e stride).counters cs 2=cs 2+cs 22 ∧
    (extractionInversePrefixLoopTemplate tm e stride).counters cs 18=cs 18+
      ((extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 22)).map (fun p => p.size+1)).sum := by
  have h := extractionInversePrefix_descending_coordinates tm e stride (cs 22) cs hlimit
  simpa only [extractionInversePrefixLoopTemplate,descendingProgramTemplate,
    Function.update_of_ne (by decide : (2 : ExtractionTraversalRegister) ≠ 22),
    Function.update_of_ne (by decide : (18 : ExtractionTraversalRegister) ≠ 22)] using h

end ShiReversibleGenerator
