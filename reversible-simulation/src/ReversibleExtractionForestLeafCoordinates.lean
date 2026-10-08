import ReversibleExtractionForestLeaf
import ReversibleExtractionInitializedPaddedCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionForestLeafTemplate_coordinates (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    let after := (extractionForestLeafTemplate tm e stride backward).counters cs
    after 0=cs 0 ∧ after 1=cs 1 ∧ after 11=cs 11 ∧ after 18=cs 18 ∧ after 26=cs 26 ∧ after 27=cs 27 := by
  let u := extractionForestLeafLoadTemplate.counters cs
  let small := fun r => u (extractionPaddedToForestRegister r)
  have hm := extractionInitializedPaddedLeafTemplate_coordinates tm e stride backward small
  dsimp only at hm
  have hp : ∀ q ∈ ([0,1,11,18] : List ExtractionPaddedRegister),
      (extractionInitializedPaddedLeafTemplate tm e stride backward).counters small q=small q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hm.1
    · exact hm.2.1
    · exact hm.2.2.1
    · exact hm.2.2.2
  have hl : ∀ q ∈ ([0,1,11,18] : List ExtractionPaddedRegister),
      (extractionForestLeafTemplate tm e stride backward).counters cs (extractionPaddedToForestRegister q)=
        u (extractionPaddedToForestRegister q) := by
    intro q hq
    have h := extractionForestLift_pull (extractionInitializedPaddedLeafTemplate tm e stride backward) u q
    rw [hp q hq] at h
    exact h
  have hu : ∀ q ∈ ([0,1,11,18,26,27] : List ExtractionForestRegister),u q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [u,extractionForestLeafLoadTemplate_counters,cleanupCounters_apply]
  have ho : ∀ q : ExtractionForestRegister,26 ≤ q.val →
      (extractionForestLeafTemplate tm e stride backward).counters cs q=u q := by
    intro q hq
    exact extractionForestLift_outside (extractionInitializedPaddedLeafTemplate tm e stride backward) u q hq
  exact ⟨(hl 0 (by simp)).trans (hu 0 (by simp)),(hl 1 (by simp)).trans (hu 1 (by simp)),
    (hl 11 (by simp)).trans (hu 11 (by simp)),(hl 18 (by simp)).trans (hu 18 (by simp)),
    (ho 26 (by decide)).trans (hu 26 (by simp)),(ho 27 (by decide)).trans (hu 27 (by simp))⟩

end ShiReversibleGenerator
