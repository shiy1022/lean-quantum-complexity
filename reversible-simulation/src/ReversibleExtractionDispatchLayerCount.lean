import ReversibleExtractionTermLayerCount
import ReversibleExtractionTermDispatchCertificate

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Every runtime guard preserves the real printer count until the selected term increments it. -/
theorem extractionTermDispatchTemplate_count (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (inputs : ExtractionTermInput tm → SymbolicWire ExtractionTermRegister)
    (cs : ExtractionTermRegister → Nat) :
    (extractionTermDispatchTemplate tm e backward inputs).counters cs 16=
      cs 16+formulaElementaryLayers (extractionTermSchema tm e (decide (cs 2=0)) (decide (cs 0 ≤ cs 2))
        (extractionRuntimeValueKind (cs 2) (cs 1))) := by
  have leaf : ∀ first endpoint value t,
      (extractionTermPrinterTemplate tm e backward first endpoint value inputs 18 extractionTermNodeRegisters).counters t 16=
        t 16+formulaElementaryLayers (extractionTermSchema tm e first endpoint value) := by
    intro first endpoint value t
    exact extractionTermPrinterTemplate_count tm e backward first endpoint value inputs 18 extractionTermNodeRegisters
      (by simp [extractionTermNodeRegisters]) (by simp [extractionTermNodeRegisters])
      (by simp [extractionTermNodeRegisters]) t
  by_cases hfirst : cs 2=0 <;> by_cases hend : cs 0 ≤ cs 2 <;>
    by_cases hvalue : cs 1 < cs 2 <;> by_cases hlo : cs 2+1 ≤ cs 1 <;> by_cases hhi : cs 1 ≤ 2*cs 2
  all_goals simp [extractionTermDispatchTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    extractionTermEndpointDispatch,extractionTermValueDispatch,guardedProgramTemplate,leaf,
    extractionTermGuardRegisters,TickIndexGuard.eval,TickIndexExpr.eval,extractionRuntimeValueKind,
    hfirst,hend,hvalue,hlo,hhi]
  all_goals split_ifs <;> simp_all [leaf]
  all_goals omega

end ShiReversibleGenerator
