import ReversibleExtractionForestLeafLoad

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Ascending inverse emission advances one padded slot and one output position after printing. -/
noncomputable def extractionForestAdvancePrograms : List (CounterProgramTemplate ExtractionForestRegister) :=
  [cleanupProgramTemplate [7],counterAffineAccumulationProgramTemplate ⟨27,18,1,1⟩ 7,
    counterAffineAccumulationProgramTemplate ⟨0,1,1,0⟩ 7]

noncomputable def extractionForestAdvanceTemplate := listProgramTemplate extractionForestAdvancePrograms

theorem extractionForestAdvanceTemplate_embeds : extractionForestAdvanceTemplate.Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  simp only [extractionForestAdvancePrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact cleanupProgramTemplate_embeds _
  all_goals exact counterAffineAccumulationProgramTemplate_embeds _ _

theorem extractionForestAdvanceTemplate_run : extractionForestAdvanceTemplate.Runs := by
  apply listProgramTemplate_run
  · intro p hp
    simp only [extractionForestAdvancePrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact cleanupProgramTemplate_embeds _
    all_goals exact counterAffineAccumulationProgramTemplate_embeds _ _
  · intro p hp
    simp only [extractionForestAdvancePrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact cleanupProgramTemplate_run _
    all_goals apply counterAffineAccumulationProgramTemplate_run <;> simp [AffineAtom.Valid]

theorem extractionForestAdvanceTemplate_ready (cs : ExtractionForestRegister → Nat) :
    extractionForestAdvanceTemplate.ready cs := by
  simp [extractionForestAdvanceTemplate,extractionForestAdvancePrograms,listProgramTemplate,sequenceProgramTemplate,
    identityProgramTemplate,cleanupProgramTemplate,counterAffineAccumulationProgramTemplate,AffineAtom.apply,cleanupCounters_apply]

theorem extractionForestAdvanceTemplate_bytes (cs : ExtractionForestRegister → Nat) :
    extractionForestAdvanceTemplate.bytes cs=[] := by
  simp [extractionForestAdvanceTemplate,extractionForestAdvancePrograms,listProgramTemplate,sequenceProgramTemplate,
    identityProgramTemplate,cleanupProgramTemplate,counterAffineAccumulationProgramTemplate]

theorem extractionForestAdvanceTemplate_counters (cs : ExtractionForestRegister → Nat) :
    extractionForestAdvanceTemplate.counters cs=Function.update
      (Function.update (cleanupCounters [7] cs) 18 (cs 18+cs 27+1)) 1 (cs 1+1) := by
  funext q
  simp only [extractionForestAdvanceTemplate,extractionForestAdvancePrograms,listProgramTemplate,
    sequenceProgramTemplate,identityProgramTemplate,cleanupProgramTemplate,counterAffineAccumulationProgramTemplate,
    AffineAtom.apply,Function.update_apply,cleanupCounters_apply]
  split_ifs <;> simp_all [cleanupCounters_apply] <;> omega

theorem extractionForestAdvanceTemplate_resources (bound : Polynomial Nat) :
    extractionForestAdvanceTemplate.CounterBound bound ∧ extractionForestAdvanceTemplate.PolynomiallyTimed bound := by
  have hb : ∀ a : AffineAtom ExtractionForestRegister, ∀ b : Polynomial Nat,
      (counterAffineAccumulationProgramTemplate a 7).CounterBound b := by
    intro a b
    refine ⟨Polynomial.C (a.coefficient+1)*b+Polynomial.C a.offset,?_⟩
    intro n cs hc q
    have hs := hc a.source
    have ht := hc a.target
    have hq := hc q
    simp only [counterAffineAccumulationProgramTemplate,AffineAtom.apply,Function.update_apply,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    split_ifs <;> nlinarith
  apply listProgramTemplate_polynomial_certificate
  · intro p hp b
    simp only [extractionForestAdvancePrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact cleanupProgramTemplate_polynomial _ b
    all_goals exact counterAffineAccumulationProgramTemplate_polynomial _ _ b
  · intro p hp b
    simp only [extractionForestAdvancePrograms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨b,by intro n cs hc q; exact cleanupCounters_uniform_bound _ cs _ hc q⟩
    all_goals exact hb _ b

end ShiReversibleGenerator
