import ReversibleExtractionBoundTermPrinter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleFormula ShiReversibleTM

/-- The actual bound printer emits the original runtime extraction term in either direction. -/
theorem extractionBoundTermPrinterTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionTermRegister → Nat) (hell : cs 2 ≤ cs 0) :
    (extractionBoundTermPrinterTemplate tm e stride backward).bytes cs=
      let p := Formula.conj (lengthFlag (extractionEmpty tm (cs 0)) (cs 2))
        (outputValue (extractionPayload tm e (cs 0)) (cs 2) (cs 1))
      let nodes := p.rawCompile
        (fun i => cs 11+stride*naturalConfigurationAddress tm (cs 0) (naturalInputAddress tm (cs 0) i)) (cs 18)
      ((if backward then nodes.reverse else nodes).map (rawAssignmentPayload backward)).flatten := by
  let after := (extractionInputSetupTemplate tm stride).counters cs
  have frame : ∀ q ∈ ([0,1,2,18] : List ExtractionTermRegister),after q=cs q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq | hq | hq | hq
    all_goals subst q
    all_goals exact extractionInputSetupTemplate_frame tm stride cs _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have h0 := frame 0 (by simp)
  have h1 := frame 1 (by simp)
  have h2 := frame 2 (by simp)
  have h18 := frame 18 (by simp)
  have hi := extractionInputSetupTemplate_inputs tm stride cs
  have h := extractionTermDispatchTemplate_selected_payload tm e backward (extractionBoundInputs tm stride) after
    (by simpa only [h2,h0] using hell) (extractionBoundInputs_stable tm stride)
    (fun p => cs 11+stride*naturalConfigurationAddress tm (cs 0) p)
    (by simpa only [after,h2,h1] using hi)
  dsimp only at h
  rw [h0,h1,h2,h18] at h
  simpa only [extractionBoundTermPrinterTemplate,sequenceProgramTemplate,
    extractionInputSetupTemplate_bytes,List.append_nil,after,h0,h1,h2,h18] using h

end ShiReversibleGenerator
