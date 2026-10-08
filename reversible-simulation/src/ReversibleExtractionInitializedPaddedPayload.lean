import ReversibleExtractionInitializedPaddedLeaf
import ReversibleExtractionPaddedLeafSetupMetadata
import ReversibleExtractionPaddedForwardPayload
import ReversibleExtractionPaddedInversePayload
import ReversibleExtractionPaddedLeafCount

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM ShiReversibleFormula

/-- The finite initialized printer emits the exact original padded compiler from arbitrary scratch counters. -/
theorem extractionInitializedPaddedLeafTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat) :
    (extractionInitializedPaddedLeafTemplate tm e stride backward).bytes cs=
      ((if backward then ((extractionFormula tm e (cs 0) (cs 1)).paddedCompile
          (fun i => cs 11+stride*i.val) (cs 18) (cs 4)).reverse
        else (extractionFormula tm e (cs 0) (cs 1)).paddedCompile
          (fun i => cs 11+stride*i.val) (cs 18) (cs 4)).map (rawAssignmentPayload backward)).flatten := by
  let t := (extractionPaddedLeafSetupTemplate tm).counters cs
  rcases extractionPaddedLeafSetupTemplate_metadata tm e cs with
    ⟨h0,h1,h4,h11,h18,hroot,hslot,h2,h9,h22,h7,h17,h20⟩
  change t 0=cs 0 at h0
  change t 1=cs 1 at h1
  change t 4=cs 4 at h4
  change t 11=cs 11 at h11
  change t 18=cs 18 at h18
  have hp : (extractionPaddedLeafTemplate tm e stride backward).bytes t=
      ((if backward then ((extractionFormula tm e (t 0) (t 1)).paddedCompile
          (fun i => t 11+stride*i.val) (t 18) (t 4)).reverse
        else (extractionFormula tm e (t 0) (t 1)).paddedCompile
          (fun i => t 11+stride*i.val) (t 18) (t 4)).map (rawAssignmentPayload backward)).flatten := by
    cases backward
    · exact extractionPaddedLeafTemplate_forward_payload tm e stride (t 4) t h2 h9 h20 hroot hslot
    · exact extractionPaddedLeafTemplate_inverse_payload tm e stride (t 4) t h2 h22 hroot hslot
  change (extractionPaddedLeafTemplate tm e stride backward).bytes t ++
    (extractionPaddedLeafSetupTemplate tm).bytes cs=_
  rw [extractionPaddedLeafSetupTemplate_bytes,List.append_nil]
  exact hp.trans (by rw [h0,h1,h4,h11,h18])

/-- Setup retains the accumulated layer count, then the actual leaf adds its formula layers and one copy. -/
theorem extractionInitializedPaddedLeafTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat) :
    (extractionInitializedPaddedLeafTemplate tm e stride backward).counters cs 16=cs 16+
      (formulaElementaryLayers (extractionFormula tm e (cs 0) (cs 1))+1) := by
  let t := (extractionPaddedLeafSetupTemplate tm).counters cs
  rcases extractionPaddedLeafSetupTemplate_metadata tm e cs with
    ⟨h0,h1,h4,h11,h18,hroot,hslot,h2,h9,h22,h7,h17,h20⟩
  have h16 : t 16=cs 16 := extractionPaddedLeafSetupTemplate_source_frame tm cs 16 (by simp)
  have hcount : (if backward then t 22 else t 9)=t 0+1 := by
    cases backward
    · exact h9
    · exact h22
  have hc := extractionPaddedLeafTemplate_count tm e stride backward t h2 hcount
  change (extractionPaddedLeafTemplate tm e stride backward).counters t 16=_
  change t 0=cs 0 at h0
  change t 1=cs 1 at h1
  exact hc.trans (by rw [h16,h0,h1])

end ShiReversibleGenerator
