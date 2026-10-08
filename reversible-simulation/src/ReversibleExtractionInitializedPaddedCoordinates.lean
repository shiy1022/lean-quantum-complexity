import ReversibleExtractionInitializedPaddedLeaf
import ReversibleExtractionPaddedLeafSetupMetadata
import ReversibleExtractionPaddedLeafFinalBase
import ReversibleExtractionPaddedLeafSourceFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Initialized leaf execution preserves its configuration source, output position and original slot base. -/
theorem extractionInitializedPaddedLeafTemplate_coordinates (tm : Turing.FinTM2)
    (e : tm.Γ tm.k₁ ≃ Bool) (stride : Nat) (backward : Bool) (cs : ExtractionPaddedRegister → Nat) :
    let after := (extractionInitializedPaddedLeafTemplate tm e stride backward).counters cs
    after 0=cs 0 ∧ after 1=cs 1 ∧ after 11=cs 11 ∧ after 18=cs 18 := by
  let t := (extractionPaddedLeafSetupTemplate tm).counters cs
  have hf : ∀ q ∈ ([0,1,11] : List ExtractionPaddedRegister),
      (extractionPaddedLeafTemplate tm e stride backward).counters t q=cs q := by
    intro q hq
    exact (extractionPaddedLeafTemplate_source_frame tm e stride backward t q hq).trans
      (extractionPaddedLeafSetupTemplate_source_frame tm cs q (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto))
  rcases extractionPaddedLeafSetupTemplate_metadata tm e cs with
    ⟨h0,h1,h4,h11,h18,hroot,hslot,h2,h9,h22,h7,h17,h20⟩
  have hcount : (if backward then t 22 else t 9)=t 0+1 := by
    cases backward
    · exact h9
    · exact h22
  have hbase := extractionPaddedLeafTemplate_base tm e stride backward t h2 hcount
  exact ⟨hf 0 (by simp),hf 1 (by simp),hf 11 (by simp),hbase.trans h18⟩

end ShiReversibleGenerator
