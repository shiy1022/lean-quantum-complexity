import ReversibleExtractionTermDispatch
import ReversibleFormulaPrinterRun

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ShiReversibleGenerator
open ShiReversibleTM
variable {R : Type} [DecidableEq R]

theorem extractionTermPrinterTemplate_frame (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward first endpoint : Bool) (value : ExtractionValueKind)
    (inputs : ExtractionTermInput tm → SymbolicWire R) (base : R) (r : NodePrinterRegisters R)
    (s : R) (hp : s ≠ r.p) (hq : s ≠ r.q) (hr : s ≠ r.r) (hc : s ≠ r.count) (cs : R → Nat) :
    (extractionTermPrinterTemplate tm e backward first endpoint value inputs base r).counters cs s=cs s :=
  fixedNodeCounters_other r _ s hp hq hr hc cs

/-- Runtime guard dispatch frames every counter outside the cached length and the fixed node fields/count. -/
theorem extractionTermDispatchTemplate_frame (tm : Turing.FinTM2) (e : tm.Γ tm.k₁ ≃ Bool)
    (backward : Bool) (inputs : ExtractionTermInput tm → SymbolicWire ExtractionTermRegister)
    (cs : ExtractionTermRegister → Nat) (q : ExtractionTermRegister)
    (h3 : q ≠ 3) (h13 : q ≠ 13) (h14 : q ≠ 14) (h15 : q ≠ 15) (h16 : q ≠ 16) :
    (extractionTermDispatchTemplate tm e backward inputs).counters cs q=cs q := by
  have leaf : ∀ first endpoint value t,
      (extractionTermPrinterTemplate tm e backward first endpoint value inputs 18 extractionTermNodeRegisters).counters t q=t q := by
    intro first endpoint value t
    exact extractionTermPrinterTemplate_frame tm e backward first endpoint value inputs 18 extractionTermNodeRegisters q h13 h14 h15 h16 t
  simp only [extractionTermDispatchTemplate,sequenceProgramTemplate,counterAffineCopyProgramTemplate,
    extractionTermEndpointDispatch,extractionTermValueDispatch,guardedProgramTemplate]
  split_ifs <;> simp [leaf,h3]

end ShiReversibleGenerator
