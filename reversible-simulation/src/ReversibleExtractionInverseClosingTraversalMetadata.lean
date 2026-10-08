import ReversibleExtractionInverseClosingLoop

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

theorem extractionInverseClosingTraversalStepTemplate_metadata (tm : Turing.FinTM2)
    (cs : ExtractionTraversalRegister → Nat) :
    let after := (extractionInverseClosingTraversalStepTemplate tm).counters cs
    after 0=cs 0 ∧ after 1=cs 1 ∧ after 2=cs 2-1 ∧
      after 18=cs 18-(extractionSizeContribution tm (cs 2) (cs 1)-3) ∧ after 20=cs 20+3 := by
  have hf : ∀ q ∈ ([0,1] : List ExtractionTermRegister),
      (extractionInverseClosingTraversalStepTemplate tm).counters cs (extractionTermToTraversalRegister q)=
        cs (extractionTermToTraversalRegister q) := by
    intro q hq
    have h := extractionTraversalLift_pull (extractionInverseClosingStepTemplate tm) cs q
    rw [extractionInverseClosingStepTemplate_source_frame tm _ q
      (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto)] at h
    exact h
  refine ⟨hf 0 (by simp),hf 1 (by simp),?_,?_,?_⟩
  · have h := extractionTraversalLift_pull (extractionInverseClosingStepTemplate tm) cs 2
    rw [(extractionInverseClosingStepTemplate_metadata tm _).1] at h
    exact h
  · have h := extractionTraversalLift_pull (extractionInverseClosingStepTemplate tm) cs 18
    rw [(extractionInverseClosingStepTemplate_metadata tm _).2.1] at h
    exact h
  · have h := extractionTraversalLift_pull (extractionInverseClosingStepTemplate tm) cs 20
    rw [(extractionInverseClosingStepTemplate_metadata tm _).2.2] at h
    exact h

end ShiReversibleGenerator
