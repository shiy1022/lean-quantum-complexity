import ReversibleExtractionForestStep
import ReversibleExtractionForestLeafCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Each actual forest step keeps its loop and padding counters and moves to the next original output slot. -/
theorem extractionForestStepTemplate_metadata (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    let after := (extractionForestStepTemplate tm e stride backward).counters cs
    after 0=cs 0 ∧ after 1=(if backward then cs 1+1 else cs 1-1) ∧ after 11=cs 11 ∧
      after 18=(if backward then cs 18+cs 27+1 else cs 18-(cs 27+1)) ∧ after 26=cs 26 ∧ after 27=cs 27 := by
  cases backward
  · let t := extractionForestRetreatTemplate.counters cs
    let u := (extractionForestLeafTemplate tm e stride false).counters t
    have hm := extractionForestLeafTemplate_coordinates tm e stride false t
    change u 0=t 0 ∧ u 1=t 1 ∧ u 11=t 11 ∧ u 18=t 18 ∧ u 26=t 26 ∧ u 27=t 27 at hm
    rcases hm with ⟨h0,h1,h11,h18,h26,h27⟩
    have ht : ∀ q ∈ ([0,1,11,26,27] : List ExtractionForestRegister),t q=cs q := by
      intro q hq
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl
      all_goals simp [t,extractionForestRetreatTemplate_counters,cleanupCounters_apply]
    have ht18 : t 18=cs 18-(cs 27+1) := by simp [t,extractionForestRetreatTemplate_counters]
    have hc : (extractionForestStepTemplate tm e stride false).counters cs=Function.update u 1 (u 1-1) := rfl
    dsimp only
    rw [hc]
    simp [h0,h1,h11,h18,h26,h27,ht 0 (by simp),ht 1 (by simp),ht 11 (by simp),ht 26 (by simp),ht 27 (by simp),ht18]
  · let t := (extractionForestLeafTemplate tm e stride true).counters cs
    have hm := extractionForestLeafTemplate_coordinates tm e stride true cs
    change t 0=cs 0 ∧ t 1=cs 1 ∧ t 11=cs 11 ∧ t 18=cs 18 ∧ t 26=cs 26 ∧ t 27=cs 27 at hm
    rcases hm with ⟨h0,h1,h11,h18,h26,h27⟩
    have hc : (extractionForestStepTemplate tm e stride true).counters cs=extractionForestAdvanceTemplate.counters t := rfl
    dsimp only
    rw [hc,extractionForestAdvanceTemplate_counters]
    simp [cleanupCounters_apply,h0,h1,h11,h18,h26,h27]

end ShiReversibleGenerator
