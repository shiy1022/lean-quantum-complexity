import ReversibleExtractionClosingAdvance
import ReversibleDecrementProgramTemplate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- The inverse closing pass moves the suffix endpoint forward and the selected length backward. -/
noncomputable def extractionInverseClosingAdvanceTemplate : CounterProgramTemplate ExtractionTermRegister :=
  sequenceProgramTemplate (counterAffineAccumulationProgramTemplate ⟨0,20,3,0⟩ 7)
    (decrementProgramTemplate 2)

theorem extractionInverseClosingAdvanceTemplate_embeds : extractionInverseClosingAdvanceTemplate.Embeds :=
  sequenceProgramTemplate_embeds _ _ (counterAffineAccumulationProgramTemplate_embeds _ _)
    (decrementProgramTemplate_embeds _)

theorem extractionInverseClosingAdvanceTemplate_run : extractionInverseClosingAdvanceTemplate.Runs :=
  sequenceProgramTemplate_run _ _ (counterAffineAccumulationProgramTemplate_embeds _ _)
    (counterAffineAccumulationProgramTemplate_run _ _ (by simp [AffineAtom.Valid]))
    (decrementProgramTemplate_run _)

theorem extractionInverseClosingAdvanceTemplate_counters (cs : ExtractionTermRegister → Nat) :
    extractionInverseClosingAdvanceTemplate.counters cs=
      Function.update (Function.update cs 20 (cs 20+3)) 2 (cs 2-1) := by
  simp [extractionInverseClosingAdvanceTemplate,sequenceProgramTemplate,
    counterAffineAccumulationProgramTemplate,AffineAtom.apply,decrementProgramTemplate]

theorem extractionInverseClosingAdvanceTemplate_ready (cs : ExtractionTermRegister → Nat) (h7 : cs 7=0) :
    extractionInverseClosingAdvanceTemplate.ready cs := by
  simp [extractionInverseClosingAdvanceTemplate,sequenceProgramTemplate,
    counterAffineAccumulationProgramTemplate,decrementProgramTemplate,h7]

theorem extractionInverseClosingAdvanceTemplate_bytes (cs : ExtractionTermRegister → Nat) :
    extractionInverseClosingAdvanceTemplate.bytes cs=[] := by
  simp [extractionInverseClosingAdvanceTemplate,sequenceProgramTemplate,
    counterAffineAccumulationProgramTemplate,decrementProgramTemplate]

theorem extractionInverseClosingAdvanceTemplate_polynomial (bound : Polynomial Nat) :
    extractionInverseClosingAdvanceTemplate.PolynomiallyTimed bound := by
  unfold extractionInverseClosingAdvanceTemplate
  apply sequenceProgramTemplate_polynomial _ _ bound (bound+Polynomial.C 3)
  · exact counterAffineAccumulationProgramTemplate_polynomial _ _ _
  · intro n cs hb hr q
    simp only [counterAffineAccumulationProgramTemplate,AffineAtom.apply,
      Polynomial.eval_add,Polynomial.eval_C]
    by_cases hq : q=(20 : ExtractionTermRegister)
    · subst q; simp; have h := hb 20; omega
    · rw [Function.update_of_ne hq]; exact (hb q).trans (by omega)
  · exact decrementProgramTemplate_polynomial _ _

end ShiReversibleGenerator
