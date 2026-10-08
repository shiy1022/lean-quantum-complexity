import ReversibleExtractionClosingAdvance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Ascending prefix traversal advances the base by the actual term size plus one, then advances length. -/
noncomputable def extractionPrefixAdvanceTemplate : CounterProgramTemplate ExtractionTermRegister :=
  sequenceProgramTemplate (counterAffineCopyProgramTemplate 12 8 7 0 1 3)
    (sequenceProgramTemplate (counterAffineAccumulationProgramTemplate ⟨8,18,0,1⟩ 7)
      (counterAffineAccumulationProgramTemplate ⟨0,2,1,0⟩ 7))

theorem extractionPrefixAdvanceTemplate_embeds : extractionPrefixAdvanceTemplate.Embeds := by
  unfold extractionPrefixAdvanceTemplate
  repeat' first
    | apply sequenceProgramTemplate_embeds
    | apply counterAffineCopyProgramTemplate_embeds
    | apply counterAffineAccumulationProgramTemplate_embeds

theorem extractionPrefixAdvanceTemplate_run : extractionPrefixAdvanceTemplate.Runs := by
  unfold extractionPrefixAdvanceTemplate
  repeat' first
    | apply sequenceProgramTemplate_run
    | apply sequenceProgramTemplate_embeds
    | apply counterAffineCopyProgramTemplate_embeds
    | apply counterAffineAccumulationProgramTemplate_embeds
    | (apply counterAffineCopyProgramTemplate_run <;> decide)
    | (apply counterAffineAccumulationProgramTemplate_run <;> simp [AffineAtom.Valid])

theorem extractionPrefixAdvanceTemplate_counters (cs : ExtractionTermRegister → Nat) :
    extractionPrefixAdvanceTemplate.counters cs=
      Function.update (Function.update (Function.update cs 8 (cs 12-3)) 18 (cs 18+(cs 12-3))) 2 (cs 2+1) := by
  funext q
  simp [extractionPrefixAdvanceTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.apply,Function.update_apply]
  all_goals split_ifs <;> simp_all <;> omega

theorem extractionPrefixAdvanceTemplate_ready (cs : ExtractionTermRegister → Nat) (h7 : cs 7=0) :
    extractionPrefixAdvanceTemplate.ready cs := by
  simp [extractionPrefixAdvanceTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.apply,h7]

theorem extractionPrefixAdvanceTemplate_bytes (cs : ExtractionTermRegister → Nat) :
    extractionPrefixAdvanceTemplate.bytes cs=[] := by
  simp [extractionPrefixAdvanceTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate]

theorem extractionPrefixAdvanceTemplate_polynomial (bound : Polynomial Nat) :
    extractionPrefixAdvanceTemplate.PolynomiallyTimed bound := by
  refine ⟨Polynomial.C 20*bound+Polynomial.C 20,?_⟩
  intro n cs hb hr
  have h8 := hb 8
  have h12 := hb 12
  simp [extractionPrefixAdvanceTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.steps,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C]
  omega

end ShiReversibleGenerator
