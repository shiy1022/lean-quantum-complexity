import ReversibleExtractionCleanForestStep

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

theorem extractionCleanForestStepTemplate_metadata (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    let after := (extractionCleanForestStepTemplate tm e stride backward).counters cs
    after 0=cs 0 ∧ after 1=(if backward then cs 1+1 else cs 1-1) ∧ after 11=cs 11 ∧
      after 18=(if backward then cs 18+cs 27+1 else cs 18-(cs 27+1)) ∧ after 26=cs 26 ∧ after 27=cs 27 := by
  let v := cleanupCounters extractionForestScratch cs
  let t := (extractionForestStepTemplate tm e stride backward).counters v
  have hm := extractionForestStepTemplate_metadata tm e stride backward v
  change t 0=v 0 ∧ t 1=(if backward then v 1+1 else v 1-1) ∧ t 11=v 11 ∧
    t 18=(if backward then v 18+v 27+1 else v 18-(v 27+1)) ∧ t 26=v 26 ∧ t 27=v 27 at hm
  change cleanupCounters extractionForestScratch t 0=cs 0 ∧
    cleanupCounters extractionForestScratch t 1=(if backward then cs 1+1 else cs 1-1) ∧
    cleanupCounters extractionForestScratch t 11=cs 11 ∧
    cleanupCounters extractionForestScratch t 18=(if backward then cs 18+cs 27+1 else cs 18-(cs 27+1)) ∧
    cleanupCounters extractionForestScratch t 26=cs 26 ∧ cleanupCounters extractionForestScratch t 27=cs 27
  simpa only [v,extractionForestScratch_frame _ 0 (by decide),extractionForestScratch_frame _ 1 (by decide),
    extractionForestScratch_frame _ 11 (by decide),extractionForestScratch_frame _ 18 (by decide),
    extractionForestScratch_frame _ 26 (by decide),extractionForestScratch_frame _ 27 (by decide)] using hm

theorem extractionCleanForestStepTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionCleanForestStepTemplate tm e stride backward).counters cs 16=cs 16+
      (formulaElementaryLayers (extractionFormula tm e (cs 0) (cs 1))+1) := by
  change cleanupCounters extractionForestScratch
    ((extractionForestStepTemplate tm e stride backward).counters (cleanupCounters extractionForestScratch cs)) 16=_
  rw [extractionForestScratch_frame _ 16 (by decide),extractionForestStepTemplate_count,
    extractionForestScratch_frame _ 16 (by decide),extractionForestScratch_frame _ 0 (by decide),
    extractionForestScratch_frame _ 1 (by decide)]

/-- The added administrative cleanup leaves the exact existing compiler payload unchanged. -/
theorem extractionCleanForestStepTemplate_bytes (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionCleanForestStepTemplate tm e stride backward).bytes cs=
      (extractionForestStepTemplate tm e stride backward).bytes cs := by
  let v := cleanupCounters extractionForestScratch cs
  have hc : (extractionCleanForestStepTemplate tm e stride backward).bytes cs=
      (extractionForestStepTemplate tm e stride backward).bytes v := by
    simp [extractionCleanForestStepTemplate,listProgramTemplate,sequenceProgramTemplate,identityProgramTemplate,cleanupProgramTemplate,v]
  rw [hc,extractionForestStepTemplate_payload,extractionForestStepTemplate_payload]
  simp only [v,extractionForestScratch_frame _ 0 (by decide),extractionForestScratch_frame _ 1 (by decide),
    extractionForestScratch_frame _ 11 (by decide),extractionForestScratch_frame _ 18 (by decide),
    extractionForestScratch_frame _ 27 (by decide)]
  rfl

end ShiReversibleGenerator
