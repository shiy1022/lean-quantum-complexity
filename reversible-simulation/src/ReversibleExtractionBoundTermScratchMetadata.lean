import ReversibleExtractionBoundTermFrames

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator

/-- Dispatch stores the exact doubled length, while every leaf frames the cache register. -/
theorem extractionTermDispatchTemplate_cache (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (inputs : ExtractionTermInput tm → SymbolicWire ExtractionTermRegister)
    (cs : ExtractionTermRegister → Nat) :
    (extractionTermDispatchTemplate tm e backward inputs).counters cs 3=2*cs 2 := by
  have leaf : ∀ first endpoint value t,
      (extractionTermPrinterTemplate tm e backward first endpoint value inputs 18 extractionTermNodeRegisters).counters t 3=t 3 := by
    intro first endpoint value t
    exact extractionTermPrinterTemplate_frame tm e backward first endpoint value inputs 18 extractionTermNodeRegisters
      3 (by decide) (by decide) (by decide) (by decide) t
  simp only [extractionTermDispatchTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    extractionTermEndpointDispatch,extractionTermValueDispatch,guardedProgramTemplate]
  split_ifs <;> simp [leaf]

/-- The real setup overwrites the index/scratch registers with bounded exact values. -/
theorem extractionBoundTermPrinterTemplate_scratch (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionTermRegister → Nat) :
    (extractionBoundTermPrinterTemplate tm e stride backward).counters cs 3=2*cs 2 ∧
    (extractionBoundTermPrinterTemplate tm e stride backward).counters cs 4=cs 1-cs 2-1 ∧
    (extractionBoundTermPrinterTemplate tm e stride backward).counters cs 7=0 ∧
    (extractionBoundTermPrinterTemplate tm e stride backward).counters cs 8=0 ∧
    (extractionBoundTermPrinterTemplate tm e stride backward).counters cs 9=0 ∧
    (extractionBoundTermPrinterTemplate tm e stride backward).counters cs 10=cs 2-1 := by
  let after := (extractionInputSetupTemplate tm stride).counters cs
  have hc := extractionTermDispatchTemplate_cache tm e backward (extractionBoundInputs tm stride) after
  have h2 : after 2=cs 2 := extractionInputSetupTemplate_frame tm stride cs 2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hf : ∀ q ∈ ([4,7,8,9,10] : List ExtractionTermRegister),
      (extractionBoundTermPrinterTemplate tm e stride backward).counters cs q=after q := by
    intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    all_goals exact (extractionTermDispatchTemplate_frame tm e backward (extractionBoundInputs tm stride) after _
      (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨by simpa only [extractionBoundTermPrinterTemplate,sequenceProgramTemplate,h2] using hc,?_,?_,?_,?_,?_⟩
  all_goals rw [hf _ (by simp)]
  all_goals simp [after,extractionInputSetupTemplate,sequenceProgramTemplate,cleanupProgramTemplate,
    cleanupCounters_apply,extractionIndexSetupTemplate_counters,extractionInputBindingTemplate,
    coordinateBindingProgramTemplate,extractionInputBindingRegisters]

end ShiReversibleGenerator
