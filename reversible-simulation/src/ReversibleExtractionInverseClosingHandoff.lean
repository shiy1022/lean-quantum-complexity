import ReversibleExtractionPassHandoff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionInverseClosingHandoffTemplate_embeds : extractionInverseClosingHandoffTemplate.Embeds :=
  sequenceProgramTemplate_embeds _ _ extractionDescendingPassHandoffTemplate_embeds
    (counterAffineCopyProgramTemplate_embeds _ _ _ _ _ _)

theorem extractionInverseClosingHandoffTemplate_run : extractionInverseClosingHandoffTemplate.Runs :=
  sequenceProgramTemplate_run _ _ extractionDescendingPassHandoffTemplate_embeds
    extractionDescendingPassHandoffTemplate_run
    (counterAffineCopyProgramTemplate_run _ _ _ _ _ _ (by decide) (by decide) (by decide))

theorem extractionInverseClosingHandoffTemplate_counters (cs : ExtractionTraversalRegister → Nat) :
    extractionInverseClosingHandoffTemplate.counters cs=
      Function.update (Function.update (Function.update (cleanupCounters [7] cs)
        2 (cs 0)) 22 (cs 0+1)) 20 (cs 18+3) := by
  simp [extractionInverseClosingHandoffTemplate,sequenceProgramTemplate,
    extractionDescendingPassHandoffTemplate_counters,counterAffineCopyProgramTemplate,cleanupCounters_apply]

theorem extractionInverseClosingHandoffTemplate_ready (cs : ExtractionTraversalRegister → Nat) :
    extractionInverseClosingHandoffTemplate.ready cs := by
  refine ⟨extractionDescendingPassHandoffTemplate_ready cs,?_⟩
  simp [counterAffineCopyProgramTemplate,extractionDescendingPassHandoffTemplate_counters,cleanupCounters_apply]

theorem extractionInverseClosingHandoffTemplate_bytes (cs : ExtractionTraversalRegister → Nat) :
    extractionInverseClosingHandoffTemplate.bytes cs=[] := by
  simp [extractionInverseClosingHandoffTemplate,sequenceProgramTemplate,
    extractionDescendingPassHandoffTemplate_bytes,counterAffineCopyProgramTemplate]

theorem extractionInverseClosingHandoffTemplate_resources (bound : Polynomial Nat) :
    extractionInverseClosingHandoffTemplate.CounterBound bound ∧
      extractionInverseClosingHandoffTemplate.PolynomiallyTimed bound := by
  obtain ⟨⟨middle,hmiddle⟩,hclock⟩ := extractionDescendingPassHandoffTemplate_resources bound
  obtain ⟨budget,hbudget⟩ := counterAffineOffsetCopyProgramTemplate_budget
    (18 : ExtractionTraversalRegister) 20 7 3 0 middle
  refine ⟨⟨budget,?_⟩,?_⟩
  · intro n cs hb q
    exact hbudget n _ (hmiddle n cs hb) q
  · exact sequenceProgramTemplate_polynomial _ _ bound middle hclock
      (fun n cs hb _ => hmiddle n cs hb) (counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ middle)

end ShiReversibleGenerator
