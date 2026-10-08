import ReversibleExtractionForestScratchCleanup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Scratch is cleared on each side of the actual slot emitter, retaining its sources and layer count. -/
noncomputable def extractionCleanForestStepTemplate (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) := listProgramTemplate
  [cleanupProgramTemplate extractionForestScratch,extractionForestStepTemplate tm e stride backward,
    cleanupProgramTemplate extractionForestScratch]

theorem extractionCleanForestStepTemplate_embeds (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionCleanForestStepTemplate tm e stride backward).Embeds := by
  apply listProgramTemplate_embeds
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact cleanupProgramTemplate_embeds _
  · exact extractionForestStepTemplate_embeds tm e stride backward
  · exact cleanupProgramTemplate_embeds _

theorem extractionCleanForestStepTemplate_run (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) : (extractionCleanForestStepTemplate tm e stride backward).Runs := by
  apply listProgramTemplate_run
  · intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact cleanupProgramTemplate_embeds _
    · exact extractionForestStepTemplate_embeds tm e stride backward
    · exact cleanupProgramTemplate_embeds _
  · intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact cleanupProgramTemplate_run _
    · exact extractionForestStepTemplate_run tm e stride backward
    · exact cleanupProgramTemplate_run _

theorem extractionCleanForestStepTemplate_ready (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionCleanForestStepTemplate tm e stride backward).ready cs :=
  ⟨trivial,extractionForestStepTemplate_ready tm e stride backward _,trivial,trivial⟩

theorem extractionCleanForestStepTemplate_resources (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (bound : Polynomial Nat) :
    (extractionCleanForestStepTemplate tm e stride backward).CounterBound bound ∧
      (extractionCleanForestStepTemplate tm e stride backward).PolynomiallyTimed bound := by
  apply listProgramTemplate_polynomial_certificate
  · intro p hp b
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact cleanupProgramTemplate_polynomial _ b
    · exact (extractionForestStepTemplate_resources tm e stride backward b).2
    · exact cleanupProgramTemplate_polynomial _ b
  · intro p hp b
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨b,by intro n cs hb q; exact cleanupCounters_uniform_bound _ cs _ hb q⟩
    · exact (extractionForestStepTemplate_resources tm e stride backward b).1
    · exact ⟨b,by intro n cs hb q; exact cleanupCounters_uniform_bound _ cs _ hb q⟩

theorem extractionCleanForestStepTemplate_scratch (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat)
    (q : ExtractionForestRegister) (hq : q ∈ extractionForestScratch) :
    (extractionCleanForestStepTemplate tm e stride backward).counters cs q=0 := by
  change cleanupCounters extractionForestScratch _ q=0
  simp [cleanupCounters_apply,hq]

end ShiReversibleGenerator
