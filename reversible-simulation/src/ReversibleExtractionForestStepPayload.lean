import ReversibleExtractionForestStepMetadata
import ReversibleExtractionForestLeafPayload

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The actual slot motion emits no gates; each step prints exactly one original padded output formula. -/
theorem extractionForestStepTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionForestStepTemplate tm e stride backward).bytes cs=
      ((if backward then ((extractionFormula tm e (cs 0) (cs 1)).paddedCompile
          (fun i => cs 11+stride*i.val) (cs 18) (cs 27)).reverse
        else (extractionFormula tm e (cs 0) (cs 1)).paddedCompile
          (fun i => cs 11+stride*i.val) (cs 18-(cs 27+1)) (cs 27)).map (rawAssignmentPayload backward)).flatten := by
  cases backward
  · let t := extractionForestRetreatTemplate.counters cs
    have h := extractionForestLeafTemplate_payload tm e stride false t
    have h0 : t 0=cs 0 := by simp [t,extractionForestRetreatTemplate_counters,cleanupCounters_apply]
    have h1 : t 1=cs 1 := by simp [t,extractionForestRetreatTemplate_counters,cleanupCounters_apply]
    have h11 : t 11=cs 11 := by simp [t,extractionForestRetreatTemplate_counters,cleanupCounters_apply]
    have h18 : t 18=cs 18-(cs 27+1) := by simp [t,extractionForestRetreatTemplate_counters]
    have h27 : t 27=cs 27 := by simp [t,extractionForestRetreatTemplate_counters,cleanupCounters_apply]
    change ([] ++ (extractionForestLeafTemplate tm e stride false).bytes t) ++ extractionForestRetreatTemplate.bytes cs=_
    rw [List.nil_append,extractionForestRetreatTemplate_bytes,List.append_nil]
    exact h.trans (by rw [h0,h1,h11,h18,h27]; simp)
  · change extractionForestAdvanceTemplate.bytes ((extractionForestLeafTemplate tm e stride true).counters cs) ++
      (extractionForestLeafTemplate tm e stride true).bytes cs=_
    rw [extractionForestAdvanceTemplate_bytes,List.nil_append]
    exact extractionForestLeafTemplate_payload tm e stride true cs

/-- Layer accounting includes the final root-to-output copy and ignores the administrative slot motion. -/
theorem extractionForestStepTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionForestStepTemplate tm e stride backward).counters cs 16=cs 16+
      (formulaElementaryLayers (extractionFormula tm e (cs 0) (cs 1))+1) := by
  cases backward
  · let t := extractionForestRetreatTemplate.counters cs
    let u := (extractionForestLeafTemplate tm e stride false).counters t
    have h := extractionForestLeafTemplate_count tm e stride false t
    change u 16=_ at h
    have h0 : t 0=cs 0 := by simp [t,extractionForestRetreatTemplate_counters,cleanupCounters_apply]
    have h1 : t 1=cs 1 := by simp [t,extractionForestRetreatTemplate_counters,cleanupCounters_apply]
    have h16 : t 16=cs 16 := by simp [t,extractionForestRetreatTemplate_counters,cleanupCounters_apply]
    change (Function.update u 1 (u 1-1)) 16=_
    simp only [Function.update_apply]
    simp only [show (16 : ExtractionForestRegister) ≠ 1 by decide,if_false]
    exact h.trans (by rw [h0,h1,h16])
  · let t := (extractionForestLeafTemplate tm e stride true).counters cs
    change extractionForestAdvanceTemplate.counters t 16=_
    rw [extractionForestAdvanceTemplate_counters]
    simp only [Function.update_apply]
    simp only [show (16 : ExtractionForestRegister) ≠ 1 by decide,
      show (16 : ExtractionForestRegister) ≠ 18 by decide,if_false]
    have h16 : cleanupCounters [7] t 16=t 16 := by simp [cleanupCounters_apply]
    rw [h16]
    exact extractionForestLeafTemplate_count tm e stride true cs

end ShiReversibleGenerator
