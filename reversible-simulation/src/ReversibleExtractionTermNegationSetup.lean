import ReversibleExtractionClosingPointerProgram

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Bind the term-root and term-negation wires from base18 and the computed size-plus-four in12. -/
noncomputable def extractionTermNegationSetupTemplate : CounterProgramTemplate ExtractionTermRegister :=
  sequenceProgramTemplate (counterAffineCopyProgramTemplate 18 21 7 0 1 0)
    (sequenceProgramTemplate (counterAffineAccumulationProgramTemplate ⟨12,21,0,1⟩ 7)
      (sequenceProgramTemplate (counterAffineCopyProgramTemplate 21 19 7 0 1 5)
        (counterAffineCopyProgramTemplate 19 21 7 1 1 0)))

theorem extractionTermNegationSetupTemplate_embeds : extractionTermNegationSetupTemplate.Embeds := by
  unfold extractionTermNegationSetupTemplate
  repeat' first
    | apply sequenceProgramTemplate_embeds
    | apply counterAffineCopyProgramTemplate_embeds
    | apply counterAffineAccumulationProgramTemplate_embeds

theorem extractionTermNegationSetupTemplate_run : extractionTermNegationSetupTemplate.Runs := by
  unfold extractionTermNegationSetupTemplate
  repeat' first
    | apply sequenceProgramTemplate_run
    | apply sequenceProgramTemplate_embeds
    | apply counterAffineCopyProgramTemplate_embeds
    | apply counterAffineAccumulationProgramTemplate_embeds
    | (apply counterAffineCopyProgramTemplate_run <;> decide)
    | (apply counterAffineAccumulationProgramTemplate_run <;> simp [AffineAtom.Valid])

theorem extractionTermNegationSetupTemplate_counters (cs : ExtractionTermRegister → Nat) :
    extractionTermNegationSetupTemplate.counters cs=
      Function.update (Function.update cs 19 (cs 18+cs 12-5)) 21 (cs 18+cs 12-5+1) := by
  simp only [extractionTermNegationSetupTemplate,sequenceProgramTemplate,
    counterAffineCopyProgramTemplate,counterAffineAccumulationProgramTemplate,AffineAtom.apply,
    Nat.one_mul,Nat.add_zero,Nat.sub_zero,Function.update_self,
    Function.update_of_ne (by decide : (12 : ExtractionTermRegister) ≠ 21)]
  funext q
  by_cases h19 : q=19 <;> by_cases h21 : q=21
  all_goals simp_all [Function.update_apply]

theorem extractionTermNegationSetupTemplate_ready (cs : ExtractionTermRegister → Nat) (h7 : cs 7=0) :
    extractionTermNegationSetupTemplate.ready cs := by
  simp [extractionTermNegationSetupTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.apply,h7]

theorem extractionTermNegationSetupTemplate_bytes (cs : ExtractionTermRegister → Nat) :
    extractionTermNegationSetupTemplate.bytes cs=[] := by
  simp [extractionTermNegationSetupTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate]

end ShiReversibleGenerator
