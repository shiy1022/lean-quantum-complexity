import ReversibleExtractionPaddedRootSetup
import ReversibleExtractionNaturalFormulaAgreement

set_option autoImplicit false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Computed whole-formula size produces both actual root addresses and both pass counters. -/
theorem extractionPaddedRootSetupTemplate_metadata (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (cs : ExtractionPaddedRegister → Nat) (hsize : cs 12=(extractionFormula tm e (cs 0) (cs 1)).size) :
    let after := extractionPaddedRootSetupTemplate.counters cs
    after 0=cs 0 ∧ after 1=cs 1 ∧ after 4=cs 4 ∧ after 11=cs 11 ∧ after 18=cs 18 ∧
      after 24=(extractionFormula tm e (after 0) (after 1)).result (after 18) ∧
      after 25=after 18+after 4 ∧ after 2=0 ∧ after 9=after 0+1 ∧ after 22=after 0+1 ∧
      after 7=0 ∧ after 17=0 ∧
      after 20=after 18+((extractionNaturalTermRange tm e (after 0) (after 1) 0 (after 0+1)).map (fun p => p.size+4)).sum := by
  dsimp only
  let after := extractionPaddedRootSetupTemplate.counters cs
  have hf : ∀ q ∈ ([0,1,4,11,18] : List ExtractionPaddedRegister),after q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals simp [after,extractionPaddedRootSetupTemplate_counters,cleanupCounters_apply]
  have h0 := hf 0 (by simp)
  have h1 := hf 1 (by simp)
  have h4 := hf 4 (by simp)
  have h11 := hf 11 (by simp)
  have h18 := hf 18 (by simp)
  change extractionPaddedRootSetupTemplate.counters cs 0=cs 0 at h0
  change extractionPaddedRootSetupTemplate.counters cs 1=cs 1 at h1
  change extractionPaddedRootSetupTemplate.counters cs 4=cs 4 at h4
  change extractionPaddedRootSetupTemplate.counters cs 11=cs 11 at h11
  change extractionPaddedRootSetupTemplate.counters cs 18=cs 18 at h18
  change after 0=cs 0 ∧ after 1=cs 1 ∧ after 4=cs 4 ∧ after 11=cs 11 ∧ after 18=cs 18 ∧ _
  refine ⟨h0,h1,h4,h11,h18,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [h0,h1,h18]
    simp [after,extractionPaddedRootSetupTemplate_counters,hsize,Formula.result]
  · rw [h18,h4]
    simp [after,extractionPaddedRootSetupTemplate_counters]
  · simp [after,extractionPaddedRootSetupTemplate_counters,cleanupCounters_apply]
  · rw [h0]
    simp [after,extractionPaddedRootSetupTemplate_counters]
  · rw [h0]
    simp [after,extractionPaddedRootSetupTemplate_counters]
  · simp [after,extractionPaddedRootSetupTemplate_counters,cleanupCounters_apply]
  · simp [after,extractionPaddedRootSetupTemplate_counters,cleanupCounters_apply]
  · rw [h18,h0,h1]
    have h20 : extractionPaddedRootSetupTemplate.counters cs 20=cs 18+cs 12-1 := by simp [after,extractionPaddedRootSetupTemplate_counters]
    rw [h20,hsize]
    have hs := extractionNaturalFormula_size tm e (cs 0) (cs 1)
    omega

end ShiReversibleGenerator
