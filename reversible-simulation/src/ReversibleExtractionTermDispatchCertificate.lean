import ReversibleExtractionTermDispatch

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM

/-- Readiness depends only on the actual guard/printer scratch counters. -/
theorem extractionTermDispatchTemplate_ready (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (inputs : ExtractionTermInput tm → SymbolicWire ExtractionTermRegister)
    (cs : ExtractionTermRegister → Nat) :
    (extractionTermDispatchTemplate tm e backward inputs).ready cs ↔
      cs 5=0 ∧ cs 6=0 ∧ cs 7=0 ∧ cs 17=0 := by
  simp [extractionTermDispatchTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    extractionTermEndpointDispatch,extractionTermValueDispatch,guardedProgramTemplate,
    extractionTermGuardRegisters,extractionTermPrinterTemplate,fixedNodeProgramTemplate,
    extractionTermNodeRegisters]
  tauto

/-- Every branch, including all runtime tests and doubled-length setup, has an actual polynomial clock. -/
theorem extractionTermDispatchTemplate_polynomial (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (inputs : ExtractionTermInput tm → SymbolicWire ExtractionTermRegister)
    (bound : Polynomial Nat) :
    (extractionTermDispatchTemplate tm e backward inputs).PolynomiallyTimed bound := by
  have leaf : ∀ first endpoint value,
      (extractionTermPrinterTemplate tm e backward first endpoint value inputs 18 extractionTermNodeRegisters).PolynomiallyTimed
        (Polynomial.C 2*bound) := by
    intro first endpoint value
    exact extractionTermPrinterTemplate_polynomial tm e backward first endpoint value inputs 18 extractionTermNodeRegisters _
  unfold extractionTermDispatchTemplate
  apply sequenceProgramTemplate_polynomial _ _ bound (Polynomial.C 2*bound)
  · exact counterAffineCopyProgramTemplate_polynomial _ _ _ _ _ _ bound
  · intro n cs hb hr q
    simp only [counterAffineCopyProgramTemplate,Polynomial.eval_mul,Polynomial.eval_C]
    by_cases hq : q=3
    · subst q; simp only [Function.update_self]; exact Nat.mul_le_mul_left 2 (hb 2)
    · rw [Function.update_of_ne hq]
      have h := hb q
      omega
  · unfold extractionTermEndpointDispatch extractionTermValueDispatch
    repeat' first
      | exact leaf _ _ _
      | apply guardedProgramTemplate_polynomial
      | (constructor <;> decide)

/-- Actual dispatch selects exactly the finite schema of the original runtime extraction term. -/
theorem extractionTermDispatchTemplate_payload (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (inputs : ExtractionTermInput tm → SymbolicWire ExtractionTermRegister)
    (cs : ExtractionTermRegister → Nat) :
    (extractionTermDispatchTemplate tm e backward inputs).bytes cs=
      (extractionTermPrinterTemplate tm e backward (decide (cs 2=0)) (decide (cs 0 ≤ cs 2))
        (extractionRuntimeValueKind (cs 2) (cs 1)) inputs 18 extractionTermNodeRegisters).bytes
        (Function.update cs 3 (2*cs 2)) := by
  by_cases hfirst : cs 2=0 <;> by_cases hend : cs 0 ≤ cs 2 <;>
    by_cases hvalue : cs 1 < cs 2 <;> by_cases hlo : cs 2+1 ≤ cs 1 <;> by_cases hhi : cs 1 ≤ 2*cs 2
  all_goals simp [extractionTermDispatchTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    extractionTermEndpointDispatch,extractionTermValueDispatch,guardedProgramTemplate,
    extractionTermGuardRegisters,TickIndexGuard.eval,TickIndexExpr.eval,extractionRuntimeValueKind,
    hfirst,hend,hvalue,hlo,hhi]
  all_goals simp_all
  all_goals omega

end ShiReversibleGenerator
