import ReversibleExtractionTermFieldBound
import ReversibleExtractionInputBinding

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

theorem extractionBoundInputs_update_cache (tm : Turing.FinTM2) (stride : Nat)
    (cs : ExtractionTermRegister → Nat) (v : Nat) (i : ExtractionTermInput tm) :
    (extractionBoundInputs tm stride i).eval (Function.update cs 3 v)=
      (extractionBoundInputs tm stride i).eval cs := by
  cases i with
  | inl i =>
    simp only [extractionBoundInputs,SymbolicWire.eval]
    split_ifs <;> simp
  | inr a => simp [extractionBoundInputs,SymbolicWire.eval]

/-- Runtime dispatch inherits one field budget for all finite branches, independent of old fields/count. -/
theorem extractionTermDispatchTemplate_fields_bound (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (stride : Nat) (backward : Bool) (cs : ExtractionTermRegister → Nat) (B : Nat)
    (hb : cs 18 ≤ B) (hi : ∀ i,(extractionBoundInputs tm stride i).eval cs ≤ B) :
    (extractionTermDispatchTemplate tm e backward (extractionBoundInputs tm stride)).counters cs 13 ≤ B+extractionTermSchemaBudget tm e ∧
    (extractionTermDispatchTemplate tm e backward (extractionBoundInputs tm stride)).counters cs 14 ≤ B+extractionTermSchemaBudget tm e ∧
    (extractionTermDispatchTemplate tm e backward (extractionBoundInputs tm stride)).counters cs 15 ≤ B+extractionTermSchemaBudget tm e := by
  let cached := Function.update cs (3 : ExtractionTermRegister) (2*cs 2)
  have leaf : ∀ first endpoint value,
      (extractionTermPrinterTemplate tm e backward first endpoint value (extractionBoundInputs tm stride)
        18 extractionTermNodeRegisters).counters cached 13 ≤ B+extractionTermSchemaBudget tm e ∧
      (extractionTermPrinterTemplate tm e backward first endpoint value (extractionBoundInputs tm stride)
        18 extractionTermNodeRegisters).counters cached 14 ≤ B+extractionTermSchemaBudget tm e ∧
      (extractionTermPrinterTemplate tm e backward first endpoint value (extractionBoundInputs tm stride)
        18 extractionTermNodeRegisters).counters cached 15 ≤ B+extractionTermSchemaBudget tm e := by
    intro first endpoint value
    apply extractionTermPrinterTemplate_fields_bound tm e backward first endpoint value
      (extractionBoundInputs tm stride) 18 extractionTermNodeRegisters
    all_goals first
      | exact extractionBoundInputs_stable tm stride
      | simpa [cached] using hb
      | (intro i; simpa only [cached,extractionBoundInputs_update_cache] using hi i)
      | simp [extractionTermNodeRegisters,NodePrinterRegisters.SourceStable]
  simp only [extractionTermDispatchTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    extractionTermEndpointDispatch,extractionTermValueDispatch,guardedProgramTemplate]
  split_ifs <;> exact leaf _ _ _

end ShiReversibleGenerator
