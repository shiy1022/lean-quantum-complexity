import ReversibleExtractionClosingSetup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Advance by term.size+1 using the computed term.size+4, retreat the endpoint by three,
and increment the runtime length index. Every arithmetic operation is a finite instruction graph. -/
noncomputable def extractionClosingAdvanceTemplate : CounterProgramTemplate ExtractionTermRegister :=
  sequenceProgramTemplate (counterAffineAccumulationProgramTemplate ⟨12,18,0,1⟩ 7)
    (sequenceProgramTemplate (counterAffineCopyProgramTemplate 18 19 7 0 1 3)
      (sequenceProgramTemplate (counterAffineCopyProgramTemplate 19 18 7 0 1 0)
        (sequenceProgramTemplate (counterAffineCopyProgramTemplate 20 21 7 0 1 3)
          (sequenceProgramTemplate (counterAffineCopyProgramTemplate 21 20 7 0 1 0)
            (counterAffineAccumulationProgramTemplate ⟨0,2,1,0⟩ 7)))))

theorem extractionClosingAdvanceTemplate_embeds : extractionClosingAdvanceTemplate.Embeds := by
  unfold extractionClosingAdvanceTemplate
  repeat' first
    | apply sequenceProgramTemplate_embeds
    | apply counterAffineCopyProgramTemplate_embeds
    | apply counterAffineAccumulationProgramTemplate_embeds

theorem extractionClosingAdvanceTemplate_run : extractionClosingAdvanceTemplate.Runs := by
  unfold extractionClosingAdvanceTemplate
  repeat' first
    | apply sequenceProgramTemplate_run
    | apply sequenceProgramTemplate_embeds
    | apply counterAffineCopyProgramTemplate_embeds
    | apply counterAffineAccumulationProgramTemplate_embeds
    | (apply counterAffineCopyProgramTemplate_run <;> decide)
    | (apply counterAffineAccumulationProgramTemplate_run <;> simp [AffineAtom.Valid])

theorem extractionClosingAdvanceTemplate_counters (cs : ExtractionTermRegister → Nat) :
    extractionClosingAdvanceTemplate.counters cs=
      Function.update (Function.update (Function.update (Function.update (Function.update cs
        18 (cs 18+cs 12-3)) 19 (cs 18+cs 12-3)) 20 (cs 20-3)) 21 (cs 20-3)) 2 (cs 2+1) := by
  funext q
  simp [extractionClosingAdvanceTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.apply,Function.update_apply]
  split_ifs <;> simp_all <;> omega

theorem extractionClosingAdvanceTemplate_ready (cs : ExtractionTermRegister → Nat) (h7 : cs 7=0) :
    extractionClosingAdvanceTemplate.ready cs := by
  simp [extractionClosingAdvanceTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.apply,h7]

theorem extractionClosingAdvanceTemplate_bytes (cs : ExtractionTermRegister → Nat) :
    extractionClosingAdvanceTemplate.bytes cs=[] := by
  simp [extractionClosingAdvanceTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate]

end ShiReversibleGenerator
