import ReversibleExtractionForestLeaf
import ReversibleExtractionInitializedPaddedPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- Dynamic padding is read from the preserved outer register, while the emitted bytes remain the original compiler bytes. -/
theorem extractionForestLeafTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionForestLeafTemplate tm e stride backward).bytes cs=
      ((if backward then ((extractionFormula tm e (cs 0) (cs 1)).paddedCompile
          (fun i => cs 11+stride*i.val) (cs 18) (cs 27)).reverse
        else (extractionFormula tm e (cs 0) (cs 1)).paddedCompile
          (fun i => cs 11+stride*i.val) (cs 18) (cs 27)).map (rawAssignmentPayload backward)).flatten := by
  let u := extractionForestLeafLoadTemplate.counters cs
  let small := fun r => u (extractionPaddedToForestRegister r)
  have hs0 : small 0=cs 0 := by simp [small,u,extractionPaddedToForestRegister,extractionForestLeafLoadTemplate_counters,cleanupCounters_apply]
  have hs1 : small 1=cs 1 := by simp [small,u,extractionPaddedToForestRegister,extractionForestLeafLoadTemplate_counters,cleanupCounters_apply]
  have hs4 : small 4=cs 27 := by simp [small,u,extractionPaddedToForestRegister,extractionForestLeafLoadTemplate_counters]
  have hs11 : small 11=cs 11 := by simp [small,u,extractionPaddedToForestRegister,extractionForestLeafLoadTemplate_counters,cleanupCounters_apply]
  have hs18 : small 18=cs 18 := by simp [small,u,extractionPaddedToForestRegister,extractionForestLeafLoadTemplate_counters,cleanupCounters_apply]
  have hp := extractionInitializedPaddedLeafTemplate_payload tm e stride backward small
  change (extractionInitializedPaddedLeafTemplate tm e stride backward).bytes small ++ extractionForestLeafLoadTemplate.bytes cs=_
  rw [extractionForestLeafLoadTemplate_bytes,List.append_nil]
  exact hp.trans (by rw [hs0,hs1,hs4,hs11,hs18])

theorem extractionForestLeafTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionForestLeafTemplate tm e stride backward).counters cs 16=cs 16+
      (formulaElementaryLayers (extractionFormula tm e (cs 0) (cs 1))+1) := by
  let u := extractionForestLeafLoadTemplate.counters cs
  let small := fun r => u (extractionPaddedToForestRegister r)
  have h := extractionForestLift_pull (extractionInitializedPaddedLeafTemplate tm e stride backward) u 16
  rw [extractionInitializedPaddedLeafTemplate_count] at h
  have hs0 : small 0=cs 0 := by simp [small,u,extractionPaddedToForestRegister,extractionForestLeafLoadTemplate_counters,cleanupCounters_apply]
  have hs1 : small 1=cs 1 := by simp [small,u,extractionPaddedToForestRegister,extractionForestLeafLoadTemplate_counters,cleanupCounters_apply]
  have hs16 : small 16=cs 16 := by simp [small,u,extractionPaddedToForestRegister,extractionForestLeafLoadTemplate_counters,cleanupCounters_apply]
  change (extractionForestLeafTemplate tm e stride backward).counters cs 16=small 16+
    (formulaElementaryLayers (extractionFormula tm e (small 0) (small 1))+1) at h
  exact h.trans (by rw [hs0,hs1,hs16])

end ShiReversibleGenerator
