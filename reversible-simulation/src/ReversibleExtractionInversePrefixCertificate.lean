import ReversibleExtractionInversePrefixLoopPayload
import ReversibleExtractionInversePrefixLoopCount
import ReversibleDescendingTemplatePointFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- One actual finite run emits the entire reversed original term-prefix pass with exact count and empty buffer. -/
theorem extractionInversePrefixLoopTemplate_counted_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (cs : ExtractionTraversalRegister → Nat) (hlimit : cs 2+cs 22 ≤ cs 0+1)
    (hb : cs 17=0) (L : Type) (caller : L → CounterInstr ExtractionTraversalRegister L) (stop : L) (ys : List Bool) :
    let p := extractionInversePrefixLoopTemplate tm e stride
    let terms := extractionNaturalTermRange tm e (cs 0) (cs 1) (cs 2) (cs 22)
    CounterRun (p.code caller stop) ⟨some (p.entry stop),cs,ys⟩ (p.steps cs)
      ⟨some (p.exit stop),p.counters cs,
        (((disjoinTermPrefix (fun bit => cs 11+stride*naturalConfigurationAddress tm (cs 0) bit)
          (cs 18) terms).reverse).map (rawAssignmentPayload true)).flatten++ys⟩ ∧
    p.counters cs 16=cs 16+(terms.map (fun p => formulaElementaryLayers p+2)).sum ∧
    p.counters cs 22=0 ∧ p.counters cs 17=0 := by
  dsimp only
  have h := extractionInversePrefixLoopTemplate_run tm e stride L caller stop cs ys
    (extractionInversePrefixLoopTemplate_ready tm e stride cs hb)
  have hp : (extractionInversePrefixLoopTemplate tm e stride).bytes cs=_ :=
    extractionInversePrefixLoop_payload tm e stride (cs 22) cs hlimit
  rw [hp] at h
  refine ⟨h,?_,?_,?_⟩
  · change Function.update (descendingTemplateCounters (extractionInversePrefixTraversalStepTemplate tm e stride)
      22 (cs 22) cs) 22 0 16=_
    rw [Function.update_of_ne (by decide : (16 : ExtractionTraversalRegister) ≠ 22)]
    exact extractionInversePrefixLoop_count tm e stride (cs 22) cs hlimit
  · simp [extractionInversePrefixLoopTemplate,descendingProgramTemplate]
  · exact (descendingProgramTemplate_point_frame (extractionInversePrefixTraversalStepTemplate tm e stride)
      22 17 (by decide) (extractionInversePrefixTraversalStepTemplate_buffer tm e stride) cs).trans hb

end ShiReversibleGenerator
