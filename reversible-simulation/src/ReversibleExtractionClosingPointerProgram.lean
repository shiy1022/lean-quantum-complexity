import ReversibleExtractionTermDispatch

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Pointer-only arithmetic is factored from size dispatch so its state can be normalized independently. -/
noncomputable def extractionClosingPointerTemplate : CounterProgramTemplate ExtractionTermRegister :=
  sequenceProgramTemplate (counterAffineCopyProgramTemplate 18 21 7 0 1 0)
    (sequenceProgramTemplate (counterAffineAccumulationProgramTemplate ⟨12,21,0,1⟩ 7)
      (sequenceProgramTemplate (counterAffineCopyProgramTemplate 21 19 7 0 1 4)
        (counterAffineCopyProgramTemplate 20 21 7 0 1 3)))

theorem extractionClosingPointerTemplate_embeds : extractionClosingPointerTemplate.Embeds := by
  unfold extractionClosingPointerTemplate
  repeat' first
    | apply sequenceProgramTemplate_embeds
    | apply counterAffineCopyProgramTemplate_embeds
    | apply counterAffineAccumulationProgramTemplate_embeds

theorem extractionClosingPointerTemplate_run : extractionClosingPointerTemplate.Runs := by
  unfold extractionClosingPointerTemplate
  repeat' first
    | apply sequenceProgramTemplate_run
    | apply sequenceProgramTemplate_embeds
    | apply counterAffineCopyProgramTemplate_embeds
    | apply counterAffineAccumulationProgramTemplate_embeds
    | (apply counterAffineCopyProgramTemplate_run <;> decide)
    | (apply counterAffineAccumulationProgramTemplate_run <;> simp [AffineAtom.Valid])

theorem extractionClosingPointerTemplate_counters (cs : ExtractionTermRegister → Nat) :
    extractionClosingPointerTemplate.counters cs=
      Function.update (Function.update cs 19 (cs 18+cs 12-4)) 21 (cs 20-3) := by
  simp only [extractionClosingPointerTemplate,sequenceProgramTemplate,
    counterAffineCopyProgramTemplate,counterAffineAccumulationProgramTemplate,AffineAtom.apply,
    Nat.one_mul,Nat.add_zero,Nat.sub_zero,Function.update_self,
    Function.update_of_ne (by decide : (12 : ExtractionTermRegister) ≠ 21),
    Function.update_of_ne (by decide : (20 : ExtractionTermRegister) ≠ 21),
    Function.update_of_ne (by decide : (20 : ExtractionTermRegister) ≠ 19)]
  funext q
  by_cases h19 : q=19 <;> by_cases h21 : q=21
  all_goals simp_all [Function.update_apply]

theorem extractionClosingPointerTemplate_ready (cs : ExtractionTermRegister → Nat) (h7 : cs 7=0) :
    extractionClosingPointerTemplate.ready cs := by
  simp [extractionClosingPointerTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.apply,h7]

theorem extractionClosingPointerTemplate_bytes (cs : ExtractionTermRegister → Nat) :
    extractionClosingPointerTemplate.bytes cs=[] := by
  simp [extractionClosingPointerTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate]

end ShiReversibleGenerator
