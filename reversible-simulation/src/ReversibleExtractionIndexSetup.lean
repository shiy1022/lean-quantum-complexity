import ReversibleExtractionTermDispatch
import ReversibleCounterPairRetreat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Runtime predecessor and payload indices are computed by copies and an actual subtraction loop. -/
noncomputable def extractionIndexSetupTemplate : CounterProgramTemplate ExtractionTermRegister :=
  sequenceProgramTemplate (counterAffineCopyProgramTemplate 2 10 7 0 1 1)
    (sequenceProgramTemplate (counterAffineCopyProgramTemplate 1 4 7 0 1 0)
      (sequenceProgramTemplate (counterAffineCopyProgramTemplate 2 9 7 1 1 0)
        (counterPairRetreatTemplate 4 8 9)))

theorem extractionIndexSetupTemplate_embeds : extractionIndexSetupTemplate.Embeds := by
  unfold extractionIndexSetupTemplate
  repeat' first
    | apply sequenceProgramTemplate_embeds
    | apply counterAffineCopyProgramTemplate_embeds
    | apply counterPairRetreatTemplate_embeds

theorem extractionIndexSetupTemplate_run : extractionIndexSetupTemplate.Runs := by
  unfold extractionIndexSetupTemplate
  repeat' first
    | apply sequenceProgramTemplate_run
    | apply sequenceProgramTemplate_embeds
    | apply counterAffineCopyProgramTemplate_embeds
    | apply counterPairRetreatTemplate_embeds
    | apply counterPairRetreatTemplate_run
    | (apply counterAffineCopyProgramTemplate_run <;> decide)

theorem extractionIndexSetupTemplate_ready (cs : ExtractionTermRegister → Nat) (h : cs 7=0) :
    extractionIndexSetupTemplate.ready cs := by
  refine ⟨h,h, h, ?_⟩
  exact counterPairRetreatTemplate_ready 4 8 9 (by decide) (by decide) _

theorem extractionIndexSetupTemplate_counters (cs : ExtractionTermRegister → Nat) :
    extractionIndexSetupTemplate.counters cs=
      Function.update (Function.update (Function.update (Function.update cs 10 (cs 2-1))
        4 (cs 1-cs 2-1)) 8 (cs 8-(cs 2+1))) 9 0 := by
  unfold extractionIndexSetupTemplate
  simp only [sequenceProgramTemplate]
  rw [counterPairRetreatTemplate_counters 4 8 9 (by decide) (by decide) (by decide)]
  simp [counterAffineCopyProgramTemplate,Nat.sub_sub,Function.update_comm]

theorem extractionIndexSetupTemplate_bytes (cs : ExtractionTermRegister → Nat) :
    extractionIndexSetupTemplate.bytes cs=[] := by
  unfold extractionIndexSetupTemplate
  simp only [sequenceProgramTemplate,counterAffineCopyProgramTemplate,List.append_nil]
  exact counterPairRetreatTemplate_bytes _ _ _ _

theorem extractionIndexSetupTemplate_polynomial (bound : Polynomial Nat) :
    extractionIndexSetupTemplate.PolynomiallyTimed bound := by
  refine ⟨Polynomial.C 40*bound+Polynomial.C 30,?_⟩
  intro n cs hb hr
  have h1 := hb 1
  have h2 := hb 2
  have h9 := hb 9
  have h10 := hb 10
  have h4 := hb 4
  unfold extractionIndexSetupTemplate
  simp only [sequenceProgramTemplate]
  rw [counterPairRetreatTemplate_steps]
  simp [counterAffineCopyProgramTemplate,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  omega

end ShiReversibleGenerator
