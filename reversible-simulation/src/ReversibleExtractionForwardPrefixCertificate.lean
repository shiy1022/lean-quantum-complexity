import ReversibleExtractionForwardPrefixLoopPayload
import ReversibleExtractionForwardPrefixLoopCount
import ReversibleDescendingTemplatePointFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- One concrete counted finite run prints the original full term-prefix compiler pass. -/
theorem extractionForwardPrefixLoopTemplate_counted_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (base : Nat)
    (hk : cs 22 ≤ cs 0+1) (hell : cs 2=cs 22-1)
    (hend : cs 18=base+((extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 22)).map (fun p => p.size+1)).sum)
    (hb : cs 17=0) (L : Type) (caller : L → CounterInstr ExtractionTraversalRegister L) (stop : L) (ys : List Bool) :
    let p := extractionForwardPrefixLoopTemplate tm e stride
    let terms := extractionNaturalTermRange tm e (cs 0) (cs 1) 0 (cs 22)
    CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
      ⟨some (p.exit stop),p.counters cs,
        ((disjoinTermPrefix (fun bit => cs 11+stride*naturalConfigurationAddress tm (cs 0) bit)
          base terms).map (rawAssignmentPayload false)).flatten++ys⟩ ∧
    p.counters cs 16=cs 16+(terms.map (fun p => formulaElementaryLayers p+2)).sum ∧
    p.counters cs 22=0 ∧ p.counters cs 17=0 := by
  dsimp only
  have h := extractionForwardPrefixLoopTemplate_run tm e stride L caller stop cs ys
    (extractionForwardPrefixLoopTemplate_ready tm e stride cs hb)
  have hp : (extractionForwardPrefixLoopTemplate tm e stride).bytes cs=_ :=
    extractionForwardPrefixLoop_payload tm e stride (cs 22) cs base hk hell hend
  rw [hp] at h
  refine ⟨h,?_,?_,?_⟩
  · change Function.update (descendingTemplateCounters (extractionForwardPrefixTraversalStepTemplate tm e stride)
      22 (cs 22) cs) 22 0 16=_
    rw [Function.update_of_ne (by decide : (16 : ExtractionTraversalRegister) ≠ 22)]
    exact extractionForwardPrefixLoop_count tm e stride (cs 22) cs hk hell
  · simp [extractionForwardPrefixLoopTemplate,descendingProgramTemplate]
  · exact (descendingProgramTemplate_point_frame (extractionForwardPrefixTraversalStepTemplate tm e stride)
      22 17 (by decide) (extractionForwardPrefixTraversalStepTemplate_buffer tm e stride) cs).trans hb

end ShiReversibleGenerator
