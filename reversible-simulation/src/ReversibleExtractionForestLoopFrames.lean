import ReversibleExtractionForestLoop
import ReversibleDescendingTemplatePointFrames

set_option autoImplicit false
namespace ShiReversibleGenerator

/-- Capacity, the input configuration address and the persistent padding bound survive the whole output forest. -/
theorem extractionForestLoopTemplate_source_frames (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    let after := (extractionForestLoopTemplate tm e stride backward).counters cs
    after 0=cs 0 ∧ after 11=cs 11 ∧ after 27=cs 27 := by
  refine ⟨?_,?_,?_⟩
  · exact descendingProgramTemplate_point_frame _ 26 0 (by decide)
      (fun t => (extractionForestStepTemplate_metadata tm e stride backward t).1) cs
  · exact descendingProgramTemplate_point_frame _ 26 11 (by decide)
      (fun t => (extractionForestStepTemplate_metadata tm e stride backward t).2.2.1) cs
  · exact descendingProgramTemplate_point_frame _ 26 27 (by decide)
      (fun t => (extractionForestStepTemplate_metadata tm e stride backward t).2.2.2.2.2) cs

theorem extractionForestLoopTemplate_remaining (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionForestRegister → Nat) :
    (extractionForestLoopTemplate tm e stride backward).counters cs 26=0 := by
  simp [extractionForestLoopTemplate,descendingProgramTemplate]

end ShiReversibleGenerator
